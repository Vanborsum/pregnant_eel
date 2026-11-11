// Build with build-static.sh. Run as root with deb-rootfs.tar beside the executable.
// Ubuntu image packages for Snap checks: snapd, ca-certificates, squashfs-tools, squashfs-tools-ng.
// Uses a trusted tarball and kernel; no host tar, mount, or chroot commands.

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <archive.h>
#include <archive_entry.h>

#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <set>
#include <utility>
#include <fcntl.h>
#include <sched.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>
#include <map>
#include <sstream>
#include <sys/mman.h>
#include <sys/sysmacros.h>

namespace fs = std::filesystem;
// Use the binary package version, including the epoch and distribution revision.
static const char* package_format = "${Package}:${Architecture}=${Version}\n";

static void prepare_downloads(const std::string& root);
static void check_elf(
    const std::string& root,
    const std::string& path);
static std::string sha256_file(
    const std::string& root,
    const std::string& path);
static std::string extract_reference(
    const std::string& root,
    const std::string& deb_path,
    const std::string& elf_path,
    const std::string& scan_path);
static std::string download_package(
    const std::string& root,
    const std::string& package,
    const std::string& path);
static void scan_directory(
    const std::string& root,
    const fs::path& directory,
    std::set<std::pair<dev_t, ino_t>>& visited);
static void expose_host_dpkg(const std::string& root);
static std::string query_owner(
    const std::string& root,
    const std::string& path,
    std::string& package_path);
static std::string capture_command(
    const std::string& root,
    const char* program,
    const std::vector<std::string>& args,
    int input_fd = -1,
    int* exit_status = nullptr);
static int run_in_rootfs(
    const std::string& root,
    const char* program,
    std::vector<std::string> args,
    int output_fd = -1,
    int input_fd = -1,
    const std::string& working_directory = "/");
static void extract_rootfs(const std::string& root, const fs::path& tar_path);
static void unmount_rootfs(const std::string& root);
static std::string mount_rootfs();
static void extract_tar(int tar_fd);
static void check_archive_path(const char* name);
static void check_archive(int status, archive* handle);
static int wait_for(pid_t pid);

// Report a failed system call. main() catches the exception and cleans up.
static void fail(const std::string& operation)
{
    const int error = errno;
    throw std::runtime_error(operation + ": " + std::strerror(error));
}

// Wait for a child and return its exit code. Retry interrupted waits.
static int wait_for(pid_t pid)
{
    int status;

    while (waitpid(pid, &status, 0) < 0) {
        if (errno != EINTR)
            fail("waitpid");
    }

    if (WIFEXITED(status))
        return WEXITSTATUS(status);

    return WIFSIGNALED(status) ? 128 + WTERMSIG(status) : 1;
}

// Turn libarchive warnings/errors into exceptions; do not use a partial rootfs.
static void check_archive(int status, archive* handle)
{
    if (status < ARCHIVE_OK) {
        const char* message = archive_error_string(handle);
        throw std::runtime_error(message ? message : "libarchive error");
    }
}

// Archive entry names and hardlink targets must stay relative to the rootfs.
static void check_archive_path(const char* name)
{
    if (!name || !*name || fs::path(name).is_absolute())
        throw std::runtime_error("Archive contains an empty or absolute path");

    for (const auto& component : fs::path(name)) {
        if (component == "..")
            throw std::runtime_error("Archive contains a '..' path component");
    }
}

// Extract an uncompressed tar into the current directory using libarchive.
// Production caller runs this in a child already chrooted into the tmpfs.
static void extract_tar(int tar_fd)
{
    archive* reader = archive_read_new();
    archive* writer = archive_write_disk_new();

    const int flags = ARCHIVE_EXTRACT_PERM | ARCHIVE_EXTRACT_TIME |
                      ARCHIVE_EXTRACT_OWNER | ARCHIVE_EXTRACT_SECURE_SYMLINKS |
                      ARCHIVE_EXTRACT_SECURE_NODOTDOT |
                      ARCHIVE_EXTRACT_SECURE_NOABSOLUTEPATHS;

    try {
        if (!reader || !writer)
            throw std::runtime_error("Cannot allocate archive reader/writer");

        check_archive(archive_read_support_filter_none(reader), reader);
        check_archive(archive_read_support_format_tar(reader), reader);
        check_archive(archive_read_open_fd(reader, tar_fd, 1024 * 1024), reader);
        check_archive(archive_write_disk_set_options(writer, flags), writer);
        // Use numeric UIDs/GIDs; do not configure username lookup.

        archive_entry* entry;
        int status;

        while ((status = archive_read_next_header(reader, &entry)) != ARCHIVE_EOF) {
            check_archive(status, reader);
            check_archive_path(archive_entry_pathname(entry));

            if (const char* target = archive_entry_hardlink(entry))
                check_archive_path(target);

            const auto type = archive_entry_filetype(entry);
            if (type != AE_IFREG && type != AE_IFDIR && type != AE_IFLNK &&
                !archive_entry_hardlink(entry)) {
                throw std::runtime_error("Archive contains a device, socket, or FIFO");
            }

            check_archive(archive_read_extract2(reader, entry, writer), reader);
        }

        check_archive(archive_write_close(writer), writer);
        check_archive(archive_read_close(reader), reader);
    } catch (...) {
        if (writer) archive_write_free(writer);
        if (reader) archive_read_free(reader);
        throw;
    }

    archive_write_free(writer);
    archive_read_free(reader);
}

// Mount a new tmpfs inside a private mount namespace. Return its absolute path.
// The outer directory stays mode 0700 even if extraction changes rootfs modes.
static std::string mount_rootfs()
{
    // Isolate this process from the inherited mount namespace.
    if (unshare(CLONE_NEWNS) < 0)
        fail("unshare (requires CAP_SYS_ADMIN)");

    // Prevent our mounts from propagating back to the host.
    if (mount(nullptr, "/", nullptr, MS_REC | MS_PRIVATE, nullptr) < 0)
        fail("make mounts private");

    char parent[] = "/var/tmp/deb-env-XXXXXX";
    if (!mkdtemp(parent))
        fail("mkdtemp");

    // make a root directory for the in-memory Debian environment
    const std::string root = std::string(parent) + "/root";

    try {
        if (mkdir(root.c_str(), 0700) < 0)
            fail("mkdir mountpoint");

        // Allow execution; ignore setuid bits and device nodes. 1 GiB ceiling for the expanded Ubuntu image with snapd.
        if (mount("tmpfs", root.c_str(), "tmpfs", MS_NOSUID | MS_NODEV,
                  "size=1G,mode=0755") < 0) {
            fail("mount tmpfs");
        }
    } catch (...) {
        rmdir(root.c_str());
        rmdir(parent);
        throw;
    }

    return root;
}

// Unmount the environment, then delete its disk-backed downloads.
static void unmount_rootfs(const std::string& root)
{
    if (root.empty())
        return;

    if (umount2(root.c_str(), MNT_DETACH) < 0) {
        std::perror("unmount rootfs");
        return;
    }

    const fs::path parent = fs::path(root).parent_path();

    std::error_code error;
    fs::remove_all(parent / "downloads", error);

    if (error) {
        std::cerr << "Cannot remove downloads: "
                  << error.message() << '\n';
    }

    rmdir(root.c_str());
    rmdir(parent.c_str());
}

// Open the tar before chroot so the child can still read it from outside.
// Only the child changes root; the parent keeps access to the host filesystem.
static void extract_rootfs(const std::string& root, const fs::path& tar_path)
{
    const int tar_fd = open(tar_path.c_str(), O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (tar_fd < 0)
        fail("open " + tar_path.string());

    std::cout.flush();
    std::cerr.flush();
    //we fork to maintain that the parent process has the true root
    const pid_t pid = fork();

    if (pid < 0) {
        const int error = errno;
        close(tar_fd);
        errno = error;
        fail("fork extractor");
    }

    if (pid == 0) {
        try {
            if (chroot(root.c_str()) < 0 || chdir("/") < 0)
                fail("enter rootfs");

            extract_tar(tar_fd);
            close(tar_fd);
            _exit(0);
        } catch (const std::exception& error) {
            std::cerr << "extract: " << error.what() << '\n';
            _exit(1);
        }
    }

    close(tar_fd);
    if (wait_for(pid) != 0)
        throw std::runtime_error("Rootfs extraction failed");
}

// Run a bundled program in a child and return its exit code.
// Arguments go directly to execve; stdin/stdout/stderr are inherited unchanged.
static int run_in_rootfs(
    const std::string& root,
    const char* program,
    std::vector<std::string> args,
    int output_fd,
    int input_fd,
    const std::string& working_directory)
{
    args.insert(args.begin(), program);
    std::vector<char*> argv;
    for (auto& arg : args)
        argv.push_back(arg.data());
    argv.push_back(nullptr);

    // Supply a clean environment instead of inheriting host loader settings.
    char path[] = "PATH=/usr/sbin:/usr/bin:/sbin:/bin";
    char home[] = "HOME=/root";
    char locale[] = "LC_ALL=C";
    char* envp[] = {path, home, locale, nullptr};

    std::cout.flush();
    std::cerr.flush();
    const pid_t pid = fork();
    if (pid < 0)
        fail("fork command");

    if (pid == 0) {

        // Redirect only when the caller supplies a descriptor.
        if ((output_fd >= 0 && dup2(output_fd, STDOUT_FILENO) < 0) ||
            (input_fd >= 0 && dup2(input_fd, STDIN_FILENO) < 0)) {
            std::perror("redirect child");
            _exit(127);
        }

        if (chroot(root.c_str()) < 0 || chdir(working_directory.c_str()) < 0) {
            std::perror("enter rootfs");
            _exit(127);
        }

        execve(program, argv.data(), envp);
        std::perror("execve");
        _exit(127);
    }

    return wait_for(pid);
}

// Run a bundled command and return stdout. Throw if the command fails.
// Stderr remains connected to the terminal.
static std::string capture_command(
    const std::string& root,
    const char* program,
    const std::vector<std::string>& args,
    int input_fd,
    int* exit_status)
{
    int fd = memfd_create("command-output", MFD_CLOEXEC);
    if (fd < 0)
        fail("memfd_create");

    std::string output;

    try {
        int status = run_in_rootfs(root, program, args, fd, input_fd);

        if (lseek(fd, 0, SEEK_SET) < 0)
            fail("rewind output");

        char buffer[4096];

        for (;;) {
            ssize_t n = read(fd, buffer, sizeof(buffer));

            if (n == 0)
                break;

            if (n < 0) {
                if (errno == EINTR)
                    continue;

                fail("read command output");
            }

            output.append(buffer, static_cast<size_t>(n));
        }

        if (exit_status)
            *exit_status = status;

        if (status != 0 && !exit_status) {
            throw std::runtime_error(
                std::string(program) + " exited " +
                std::to_string(status) + ": " + output
            );
        }
    } catch (...) {
        close(fd);
        throw;
    }

    close(fd);
    return output;
}

// Remove a single command-output newline without changing package names.
static std::string trim_newline(std::string text)
{
    if (!text.empty() && text.back() == '\n')
        text.pop_back();
    return text;
}

// Escape dpkg-query's glob syntax; filenames must be literal search terms.
static std::string escape_dpkg_pattern(const std::string& path)
{
    std::string result;
    for (char c : path) {
        if (c == '*' || c == '?' || c == '[' || c == '\\')
            result += '\\';
        result += c;
    }
    return result;
}

// Reject query patterns and APT selector syntax in metadata fields.
static bool valid_name(const std::string& value, bool architecture = false)
{
    const std::string allowed = architecture
        ? "abcdefghijklmnopqrstuvwxyz0123456789-"
        : "abcdefghijklmnopqrstuvwxyz0123456789+.-";
    return !value.empty() && value.find_first_not_of(allowed) == std::string::npos &&
           ((value[0] >= 'a' && value[0] <= 'z') ||
            (value[0] >= '0' && value[0] <= '9'));
}

// Parse name:architecture=version and validate each field before passing to APT.
static void validate_selector(const std::string& selector)
{
    const size_t colon = selector.find(':');
    const size_t equal = selector.find('=');
    if (colon == std::string::npos || equal == std::string::npos || equal <= colon)
        throw std::runtime_error("Malformed package identity");

    const std::string version = selector.substr(equal + 1);
    if (!valid_name(selector.substr(0, colon)) ||
        !valid_name(selector.substr(colon + 1, equal - colon - 1), true) ||
        version.empty() || version[0] < '0' || version[0] > '9' ||
        version.find_first_not_of(
            "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.+:~-"
        ) != std::string::npos) {
        throw std::runtime_error("Invalid package identity in database");
    }
}

// Try the real scan path first, then equivalent merged-/usr spellings.
// Only add an alias when the host directories really refer to the same inode.
static std::vector<std::string> ownership_paths(const std::string& path)
{
    std::vector<std::string> paths = {path};
    for (const std::string prefix : {"/bin", "/sbin", "/lib", "/lib32", "/lib64", "/libx32"}) {
        const std::string merged = "/usr" + prefix;
        std::error_code error;
        if (!fs::equivalent(prefix, merged, error) || error)
            continue;
        if (path.compare(0, merged.size() + 1, merged + "/") == 0)
            paths.push_back(prefix + path.substr(merged.size()));
        else if (path.compare(0, prefix.size() + 1, prefix + "/") == 0)
            paths.push_back(merged + path.substr(prefix.size()));
    }
    return paths;
}

// Parse exact ownership lines, ignoring neither diversions nor path mismatches.
// As requested, select the first owner when dpkg lists several owners.
static std::string parse_owner(const std::string& text, const std::string& path)
{
    std::istringstream lines(text);
    std::string line;
    std::string owner;
    while (std::getline(lines, line)) {
        if (line.rfind("diversion by ", 0) == 0 ||
            line.rfind("local diversion ", 0) == 0) {
            throw std::runtime_error("Diverted file needs manual ownership resolution");
        }

        const size_t separator = line.find(": ");
        if (separator == std::string::npos || line.substr(separator + 2) != path)
            continue;

        std::string name = line.substr(0, separator);
        name = name.substr(0, name.find(", "));
        const size_t colon = name.find(':');
        if (!valid_name(name.substr(0, colon)) ||
            (colon != std::string::npos && !valid_name(name.substr(colon + 1), true))) {
            throw std::runtime_error("Invalid owner name returned by dpkg-query");
        }
        if (owner.empty())
            owner = name;
    }
    return owner;
}

// Query the read-only host database, never the image's installed-package list.
// package_path preserves the database spelling for extraction from the .deb.
static std::string query_owner(
    const std::string& root,
    const std::string& path,
    std::string& package_path)
{
    if (path.find_first_of("\n\r") != std::string::npos)
        throw std::runtime_error("Cannot parse ownership of a filename containing newlines");

    for (const std::string& candidate : ownership_paths(path)) {
        int status = 0;
        const std::string result = capture_command(root, "/usr/bin/dpkg-query", {
            "--admindir=/host-dpkg", "--search", escape_dpkg_pattern(candidate)
        }, -1, &status);
        if (status != 0 && status != 1)
            throw std::runtime_error("dpkg-query failed: " + result);

        const std::string owner = parse_owner(result, candidate);
        if (owner.empty())
            continue;

        const std::string identity = trim_newline(capture_command(root, "/usr/bin/dpkg-query", {
            "--admindir=/host-dpkg", "--show",
            "--showformat=${Package}:${Architecture}=${Version}\t${db:Status-Status}\n",
            owner
        }));
        const size_t separator = identity.find('\t');
        if (separator == std::string::npos || identity.substr(separator + 1) != "installed")
            throw std::runtime_error("Owner is not in the installed state");

        const std::string selector = identity.substr(0, separator);
        validate_selector(selector);
        package_path = candidate;
        return selector;
    }
    std::cout << path << " : Failure : No Corresponding Package Identified\n";
    throw std::runtime_error("No installed dpkg owner found");
}

// Bind the host database read-only at a separate path. APT keeps the image DB.
static void expose_host_dpkg(const std::string& root)
{
    const std::string source = fs::canonical("/var/lib/dpkg").string();
    const std::string destination = root + "/host-dpkg";
    if (mkdir(destination.c_str(), 0700) < 0)
        fail("mkdir host-dpkg");
    if (mount(source.c_str(), destination.c_str(), nullptr, MS_BIND, nullptr) < 0)
        fail("bind host dpkg database");

    if (mount(nullptr, destination.c_str(), nullptr,
              MS_BIND | MS_REMOUNT | MS_RDONLY | MS_NOSUID | MS_NODEV | MS_NOEXEC,
              nullptr) < 0) {
        fail("make host dpkg database read-only");
    }
}

// Point the bundled Ubuntu archive entries at the selected US mirror.
static void configure_ubuntu_mirror(const std::string& root)
{
    // Match an entire archive URI on an active source line. Preserve the
    // suite, components, signing keys, and separate security archive.
    const std::string rewrite =
        R"(/^[[:space:]]*(URIs:|deb(-src)?[[:space:]])/)"
        R"(s@([[:space:]])https?://(us\.)?archive\.ubuntu\.com/ubuntu/?([[:space:]]|$)@\1https://us.archive.ubuntu.com/ubuntu\3@g)";

    for (const char* file : {"/etc/apt/sources.list.d/ubuntu.sources",
                             "/etc/apt/sources.list"}) {
        if (fs::is_regular_file(root + file) &&
            run_in_rootfs(root, "/usr/bin/sed", {"-E", "-i", rewrite, file}) != 0) {
            throw std::runtime_error(std::string("Cannot configure Ubuntu mirror in ") + file);
        }
    }
}

// Keep repository indexes and caches on disk too. Use only image repositories
// and keys, with authentication enabled. Run as root because our private
// per-package directories are mode 0700 and inaccessible to APT's _apt user.
static std::vector<std::string> apt_options()
{
    return {
        "-o", "Dir::State::lists=/downloads/apt-lists",
        "-o", "Dir::Cache=/downloads/apt-cache",
        "-o", "APT::Sandbox::User=root",
        "-o", "APT::Get::AllowUnauthenticated=false",
        "-o", "Acquire::AllowInsecureRepositories=false",
        "-o", "Acquire::AllowDowngradeToInsecureRepositories=false",
        "-o", "Acquire::AllowWeakRepositories=false"
    };
}

// Add installed foreign architectures to the private image DB, then refresh
// authenticated indexes once. Never run install or package maintainer scripts.
static void refresh_repositories(const std::string& root)
{
    std::istringstream lines(capture_command(root, "/usr/bin/dpkg-query", {
        "--admindir=/host-dpkg", "--show",
        "--showformat=${Architecture}\t${db:Status-Status}\n"
    }));
    std::set<std::string> architectures;
    std::string line;
    while (std::getline(lines, line)) {
        const size_t tab = line.find('\t');
        if (tab == std::string::npos || line.substr(tab + 1) != "installed")
            continue;
        const std::string arch = line.substr(0, tab);
        if (!valid_name(arch, true))
            throw std::runtime_error("Invalid architecture in host database");
        if (arch != "all")
            architectures.insert(arch);
    }
    const std::string native = trim_newline(capture_command(root, "/usr/bin/dpkg", {
        "--print-architecture"
    }));
    for (const std::string& arch : architectures) {
        if (arch != native)
            capture_command(root, "/usr/bin/dpkg", {"--add-architecture", arch});
    }

    fs::create_directories(root + "/downloads/apt-lists/partial");
    fs::create_directories(root + "/downloads/apt-cache/archives/partial");
    std::vector<std::string> args = apt_options();
    args.insert(args.end(), {"-o", "APT::Update::Error-Mode=any", "update"});
    if (run_in_rootfs(root, "/usr/bin/apt-get", args) != 0)
        throw std::runtime_error("Authenticated APT index refresh failed");
}

// Recursively scan directories without following symlinks.
// Track directory device/inode pairs to avoid revisiting bind-mounted aliases.
// Only read regular files; identify ELF candidates by their first four bytes.
static void scan_directory(
    const std::string& root,
    const fs::path& directory,
    std::set<std::pair<dev_t, ino_t>>& visited)
{
    // Skip virtual filesystems and our temporary environment.
    if (directory == "/proc" ||
        directory == "/sys" ||
        directory == "/dev" ||
        directory == fs::path(root).parent_path()) {
        return;
    }

    if (directory == "/.snapshots")
        return;

    struct stat directory_info {};

    if (lstat(directory.c_str(), &directory_info) < 0) {
        std::cerr << "Cannot inspect " << directory
                  << ": " << std::strerror(errno) << '\n';
        return;
    }

    // lstat does not follow symlinks.
    if (!S_ISDIR(directory_info.st_mode))
        return;

    if (!visited.emplace(
            directory_info.st_dev,
            directory_info.st_ino).second) {
        return;
    }

    std::error_code error;
    fs::directory_iterator iterator(directory, error);
    const fs::directory_iterator end;

    if (error) {
        std::cerr << "Cannot scan " << directory
                  << ": " << error.message() << '\n';
        return;
    }

    while (iterator != end) {
        const fs::path path = iterator->path();
        const fs::file_status status = iterator->symlink_status(error);

        if (error) {
            std::cerr << "Cannot inspect " << path
                      << ": " << error.message() << '\n';
        }
        else if (fs::is_directory(status)) {
            scan_directory(root, path, visited);
        }
        else if (fs::is_regular_file(status)) {
            // O_NOFOLLOW rejects symlinks if the file changes during scanning.
            // O_NONBLOCK avoids blocking if it is replaced with a FIFO.
            const int fd = open(
                path.c_str(),
                O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK
            );

            if (fd < 0) {
                std::cerr << "Cannot open " << path
                          << ": " << std::strerror(errno) << '\n';
            }
            else {
                struct stat file_info {};
                unsigned char magic[4];
                ssize_t count = -1;

                // Verify the opened object is still a regular file.
                if (fstat(fd, &file_info) < 0) {
                    std::cerr << "Cannot inspect opened file " << path
                              << ": " << std::strerror(errno) << '\n';
                }
                else if (S_ISREG(file_info.st_mode)) {
                    do {
                        count = pread(fd, magic, sizeof(magic), 0);
                    } while (count < 0 && errno == EINTR);

                    if (count < 0) {
                        std::cerr << "Cannot read " << path
                                  << ": " << std::strerror(errno) << '\n';
                    }
                }

                close(fd);

                if (count == 4 &&
                    magic[0] == 0x7f &&
                    magic[1] == 'E' &&
                    magic[2] == 'L' &&
                    magic[3] == 'F') {
                    //path does not need to be in our fs because we are only looking
                    //up the raw path string in the db (we're not opening the file)
                    check_elf(root, path.string());
                }
            }
        }

        // Symlinks and other non-regular objects are skipped.
        iterator.increment(error);

        if (error) {
            std::cerr << "Directory traversal failed in " << directory
                      << ": " << error.message() << '\n';
            break;
        }
    }
}

// Download the exact name:architecture=version into a private disk directory.
// APT authenticates the archive against signed repository indexes; dpkg-deb
// then confirms the identity. No package is installed or executed.
static std::string download_package(
    const std::string& root,
    const std::string& package,
    const std::string& path)
{
    static std::map<std::string, std::string> cache;
    const std::string key = root + "\n" + package;
    if (cache.count(key))
        return cache.at(key);
    validate_selector(package);

    std::string directory = root + "/downloads/package-XXXXXX";
    if (!mkdtemp(directory.data()))
        fail("mkdtemp download");
    const std::string inside = "/downloads/" + fs::path(directory).filename().string();

    try {
        std::vector<std::string> args = apt_options();
        args.insert(args.end(), {"download", "--", package});
        if (run_in_rootfs(root, "/usr/bin/apt-get", args, -1, -1, inside) != 0) {
            std::cout << path << " : Failure : Corresponding Package Failed to Download\n";
            throw std::runtime_error("Exact package download failed: " + package);
        }

        std::string found;
        for (const auto& entry : fs::directory_iterator(directory)) {
            if (!fs::is_regular_file(entry.symlink_status()) || entry.path().extension() != ".deb")
                continue;
            if (!found.empty())
                throw std::runtime_error("More than one reference .deb downloaded");
            found = inside + "/" + entry.path().filename().string();
        }
        if (found.empty())
            throw std::runtime_error("APT produced no .deb archive");

        const std::string actual = trim_newline(capture_command(root, "/usr/bin/dpkg-deb", {
            std::string("--showformat=") + package_format, "--show", found
        }));
        if (actual != package)
            throw std::runtime_error("Downloaded package identity does not match: requested [" +
                                     package + "], received [" + actual + "]");

        cache[key] = found;
        return found;
    } catch (...) {
        std::error_code ignored;
        fs::remove_all(directory, ignored);
        throw;
    }
}

// Feed the current ar member into the nested tar reader without buffering the
// full .deb or uncompressed payload. This scanner is deliberately single-threaded.
static la_ssize_t read_deb_chunk(archive* inner, void* context, const void** data)
{
    static unsigned char buffer[64 * 1024];
    archive* outer = static_cast<archive*>(context);
    const la_ssize_t count = archive_read_data(outer, buffer, sizeof(buffer));
    if (count < 0) {
        const char* message = archive_error_string(outer);
        archive_set_error(inner, EIO, "%s", message ? message : "Cannot read .deb payload");
    }
    *data = buffer;
    return count;
}

// Open data.tar[.gz/.xz/.zst/...] inside a Debian ar archive as a tar stream.
// The caller owns both readers; free the inner reader before the outer reader.
static archive* open_deb_payload(const std::string& file, archive*& outer)
{
    archive* inner = nullptr;
    outer = archive_read_new();
    if (!outer)
        throw std::runtime_error("Cannot allocate .deb reader");
    try {
        check_archive(archive_read_support_filter_none(outer), outer);
        check_archive(archive_read_support_format_ar(outer), outer);
        check_archive(archive_read_open_filename(outer, file.c_str(), 64 * 1024), outer);

        archive_entry* entry;
        int status;
        while ((status = archive_read_next_header(outer, &entry)) != ARCHIVE_EOF) {
            check_archive(status, outer);
            const char* raw = archive_entry_pathname(entry);
            const std::string name = raw ? raw : "";
            if (name != "data.tar" && name != "data.tar.gz" && name != "data.tar.xz" &&
                name != "data.tar.zst" && name != "data.tar.bz2" && name != "data.tar.lzma")
                continue;

            inner = archive_read_new();
            if (!inner)
                throw std::runtime_error("Cannot allocate payload reader");
            check_archive(archive_read_support_format_tar(inner), inner);
            check_archive(archive_read_support_filter_none(inner), inner);
            check_archive(archive_read_support_filter_gzip(inner), inner);
            check_archive(archive_read_support_filter_xz(inner), inner);
            check_archive(archive_read_support_filter_zstd(inner), inner);
            check_archive(archive_read_support_filter_bzip2(inner), inner);
            check_archive(archive_read_support_filter_lzma(inner), inner);
            check_archive(archive_read_open(inner, outer, nullptr, read_deb_chunk, nullptr), inner);
            return inner;
        }
        throw std::runtime_error("No data.tar payload in .deb");
    } catch (...) {
        if (inner) archive_read_free(inner);
        archive_read_free(outer);
        outer = nullptr;
        throw;
    }
}

// Carve only the requested regular file out of the .deb. Follow archive
// hardlinks by their archive-root-relative names; never follow symlinks.
// Write the reference to tmpfs and return its filename to the caller.
static std::string extract_reference(
    const std::string& root,
    const std::string& deb_path,
    const std::string& elf_path,
    const std::string& scan_path)
{
    if (elf_path.empty() || elf_path[0] != '/')
        throw std::runtime_error("Expected an absolute package member path");
    std::string wanted = elf_path.substr(1);
    check_archive_path(wanted.c_str());
    wanted = fs::path(wanted).lexically_normal().generic_string();

    std::set<std::string> visited;
    fs::create_directories(root + "/reference");

    for (int depth = 0; depth < 32; ++depth) {
        if (!visited.insert(wanted).second)
            throw std::runtime_error("Hardlink loop in .deb payload");

        archive* outer = nullptr;
        archive* reader = nullptr;
        int output_fd = -1;
        std::string output_path;
        bool follow_hardlink = false;
        try {
            reader = open_deb_payload(root + deb_path, outer);
            archive_entry* entry;
            int status;
            while ((status = archive_read_next_header(reader, &entry)) != ARCHIVE_EOF) {
                check_archive(status, reader);
                const char* name = archive_entry_pathname(entry);
                check_archive_path(name);
                if (fs::path(name).lexically_normal().generic_string() != wanted)
                    continue;

                if (const char* target = archive_entry_hardlink(entry)) {
                    check_archive_path(target);
                    wanted = fs::path(target).lexically_normal().generic_string();
                    follow_hardlink = true;
                    break;
                }
                if (archive_entry_filetype(entry) != AE_IFREG || archive_entry_symlink(entry))
                    throw std::runtime_error("Reference member is not a regular file");

                output_path = root + "/reference/elf-XXXXXX";
                output_fd = mkstemp(output_path.data());
                if (output_fd < 0)
                    fail("mkstemp reference");
                if (fcntl(output_fd, F_SETFD, FD_CLOEXEC) < 0)
                    fail("set reference close-on-exec");
                check_archive(archive_read_data_into_fd(reader, output_fd), reader);
                const int close_status = close(output_fd);
                output_fd = -1;
                if (close_status < 0)
                    fail("close reference");

                archive_read_free(reader);
                archive_read_free(outer);
                return output_path;
            }
            if (!follow_hardlink) {
                // Existing consumers expect this exact legacy status line.
                std::cout << scan_path << " : Failure : Binary Could Not be Parsed From rpm Archive\n";
                throw std::runtime_error("ELF path is absent from the .deb payload: " + elf_path);
            }
        } catch (...) {
            if (output_fd >= 0) close(output_fd);
            if (!output_path.empty()) unlink(output_path.c_str());
            if (reader) archive_read_free(reader);
            if (outer) archive_read_free(outer);
            throw;
        }
        archive_read_free(reader);
        archive_read_free(outer);
    }
    throw std::runtime_error("Too many hardlink indirections in .deb");
}

// Hash a host file with the trusted image's sha256sum.
static std::string sha256_file(
    const std::string& root,
    const std::string& path)
{
    int fd = open(
        path.c_str(),
        O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK
    );

    if (fd < 0)
        fail("open " + path);

    std::string digest;

    try {
        struct stat before {}, after {};

        if (fstat(fd, &before) < 0)
            fail("fstat");

        if (!S_ISREG(before.st_mode))
            throw std::runtime_error("Target is no longer a regular file");

        std::istringstream output(capture_command(
            root, "/usr/bin/sha256sum", {"-"}, fd
        ));

        output >> digest;

        if (digest.size() != 64 ||
            digest.find_first_not_of("0123456789abcdef") != std::string::npos) {
            throw std::runtime_error("Invalid sha256sum output");
        }

        if (fstat(fd, &after) < 0)
            fail("fstat");

        if (before.st_size != after.st_size ||
            before.st_mtim.tv_sec != after.st_mtim.tv_sec ||
            before.st_mtim.tv_nsec != after.st_mtim.tv_nsec ||
            before.st_ctim.tv_sec != after.st_ctim.tv_sec ||
            before.st_ctim.tv_nsec != after.st_ctim.tv_nsec) {
            throw std::runtime_error("Target changed while being hashed");
        }
    } catch (...) {
        close(fd);
        throw;
    }

    close(fd);
    return digest;
}

// Extract printable ASCII strings from a regular file.
// Like strings -a with a minimum length of 4; does not decode UTF-16/UTF-32.
static std::vector<std::string> extract_strings(const std::string& path)
{
    constexpr size_t minimum_length = 4;

    int fd = open(
        path.c_str(),
        O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK
    );

    if (fd < 0)
        fail("open " + path);

    std::vector<std::string> strings;
    std::string current;

    try {
        struct stat before {}, after {};

        if (fstat(fd, &before) < 0)
            fail("fstat");

        if (!S_ISREG(before.st_mode))
            throw std::runtime_error("Target is no longer a regular file");

        unsigned char buffer[64 * 1024];

        for (;;) {
            ssize_t count = read(fd, buffer, sizeof(buffer));

            if (count < 0) {
                if (errno == EINTR)
                    continue;

                fail("read " + path);
            }

            if (count == 0)
                break;

            for (ssize_t i = 0; i < count; ++i) {
                const unsigned char byte = buffer[i];

                const bool printable =
                    (byte >= 0x20 && byte <= 0x7e) || byte == '\t';

                if (printable) {
                    current.push_back(static_cast<char>(byte));
                }
                else {
                    if (current.size() >= minimum_length)
                        strings.push_back(current);

                    current.clear();
                }
            }
        }

        // Include a final string even when the file ends without a delimiter.
        if (current.size() >= minimum_length)
            strings.push_back(current);

        if (fstat(fd, &after) < 0)
            fail("fstat");

        if (before.st_size != after.st_size ||
            before.st_mtim.tv_sec != after.st_mtim.tv_sec ||
            before.st_mtim.tv_nsec != after.st_mtim.tv_nsec ||
            before.st_ctim.tv_sec != after.st_ctim.tv_sec ||
            before.st_ctim.tv_nsec != after.st_ctim.tv_nsec) {
            throw std::runtime_error(
                "Target changed while extracting strings"
            );
        }
    } catch (...) {
        close(fd);
        throw;
    }

    close(fd);
    return strings;
}

// Multiply the fraction of strings found in each direction, counting repeated entries.
static float score_string_overlap(
    const std::vector<std::string>& reference_strings,
    const std::vector<std::string>& actual_strings)
{
    if (reference_strings.empty())
        return 0.0f;
    if (actual_strings.empty())
        return 0.0f;

    float first_percentage = 0.0;
    float second_percentage = 0.0;
    float numerator = 0.0;
    float denominator = 0.0;

    for (const std::string& s : reference_strings)
    {
        int found = 0;
        for (const std::string& candidate : actual_strings)
        {
            if (candidate == s)
            {
                found = 1;
                break;
            }
        }
        if (found) numerator += 1.0;
        denominator += 1.0;
    }

    first_percentage = numerator / denominator;
    numerator = 0.0;
    denominator = 0.0;

    for (const std::string& s : actual_strings)
    {
        int found = 0;
        for (const std::string& candidate : reference_strings)
        {
            if (candidate == s)
            {
                found = 1;
                break;
            }
        }
        if (found) numerator += 1.0;
        denominator += 1.0;
    }

    second_percentage = numerator / denominator;
    return first_percentage * second_percentage;
}

// Split /snap/<store-name>[_<instance>]/<store-revision>/<member>.
// Parallel instances share the same Store archive for a given revision.
static void parse_snap_path(
    const std::string& path,
    std::string& name,
    std::string& revision,
    std::string& member)
{
    const size_t name_end = path.find('/', 6);
    if (name_end == std::string::npos || path.compare(0, 6, "/snap/") != 0)
        throw std::runtime_error("Expected /snap/<name>/<revision>/<file>");
    const size_t revision_end = path.find('/', name_end + 1);
    if (revision_end == std::string::npos || revision_end + 1 == path.size())
        throw std::runtime_error("Expected /snap/<name>/<revision>/<file>");

    const std::string instance = path.substr(6, name_end - 6);
    const size_t split = instance.find('_');
    name = instance.substr(0, split);
    const std::string letters = "abcdefghijklmnopqrstuvwxyz";
    const std::string alnum = letters + "0123456789";
    if (name.size() < 2 || name.size() > 40 || name.front() == '-' || name.back() == '-' ||
        name.find_first_of(letters) == std::string::npos ||
        name.find_first_not_of(alnum + "-") != std::string::npos ||
        name.find("--") != std::string::npos)
        throw std::runtime_error("Invalid Snap Store name");

    if (split != std::string::npos) {
        const std::string key = instance.substr(split + 1);
        if (key.empty() || key.size() > 10 || key.find_first_not_of(alnum) != std::string::npos)
            throw std::runtime_error("Invalid Snap instance key");
    }

    revision = path.substr(name_end + 1, revision_end - name_end - 1);
    if (revision.empty() || revision.front() == '0' ||
        revision.find_first_not_of("0123456789") != std::string::npos)
        throw std::runtime_error("Expected a numeric Store revision (local snaps and components are unsupported)");

    member = path.substr(revision_end + 1);
    check_archive_path(member.c_str());
}

// Fetch once per (name, revision) into the private disk cache. The trusted
// client's download command fetches and verifies the Store assertions itself.
// Its default filenames identify the returned name and revision. Accept only
// the expected pair in our fresh directory. Never install or execute the snap.
static std::string download_snap(const std::string& root, const std::string& name,
                                 const std::string& revision)
{
    static std::map<std::string, std::string> archives;
    static std::map<std::string, std::string> failures;
    const std::string stem = name + "_" + revision;
    const std::string key = root + "/" + stem;
    if (archives.count(key))
        return archives.at(key);
    if (failures.count(key))
        throw std::runtime_error(failures.at(key));

    std::string directory = root + "/downloads/snap-XXXXXX";
    if (!mkdtemp(directory.data()))
        fail("mkdtemp snap download");

    try {
        for (const char* program : {"/usr/bin/snap", "/usr/bin/unsquashfs", "/usr/bin/rdsquashfs"}) {
            if (access((root + program).c_str(), X_OK) < 0)
                throw std::runtime_error(std::string("Missing Snap tool in deb-rootfs.tar: ") + program);
        }

        const std::string inside = "/downloads/" + fs::path(directory).filename().string();
        if (run_in_rootfs(root, "/usr/bin/snap",
                          {"download", "--revision=" + revision, name}, -1, -1, inside) != 0)
            throw std::runtime_error("Snap Store download or assertion verification failed for " + stem);

        for (const char* ext : {".snap", ".assert"}) {
            const fs::path file = fs::path(directory) / (stem + ext);
            if (!fs::is_regular_file(fs::symlink_status(file)) || fs::file_size(file) == 0)
                throw std::runtime_error("Missing exact verified Snap download: " + stem + ext);
        }
        const std::string archive = inside + "/" + stem + ".snap";
        archives[key] = archive;
        return archive;
    } catch (const std::exception& error) {
        std::error_code ignored;
        fs::remove_all(directory, ignored);
        failures[key] = error.what();
        throw;
    }
}

// Read one literal regular-file member from the authenticated SquashFS.
// Keep even large reference binaries on disk. check_elf removes this copy.
static std::string extract_snap_reference(const std::string& root, const std::string& path)
{
    std::string name, revision, member;
    parse_snap_path(path, name, revision, member);
    const std::string archive = download_snap(root, name, revision);
    std::string reference = root + "/downloads/snap-elf-XXXXXX";
    const int fd = mkostemp(reference.data(), O_CLOEXEC);
    if (fd < 0)
        fail("mkostemp snap reference");

    try {
        if (run_in_rootfs(root, "/usr/bin/rdsquashfs", {"--cat", "/" + member, archive}, fd) != 0)
            throw std::runtime_error("Cannot extract regular file from verified snap: " + member);
    } catch (...) {
        close(fd);
        unlink(reference.c_str());
        throw;
    }
    if (close(fd) < 0) {
        const int error = errno;
        unlink(reference.c_str());
        errno = error;
        fail("close snap reference");
    }
    return reference;
}

// Look up, download, and compare one detected ELF.
// A failed lookup/download is unresolved, not a hash mismatch.
static void check_elf(
    const std::string& root,
    const std::string& path)
{
    try {
        std::string reference;
        if (path.compare(0, 6, "/snap/") == 0) {
            reference = extract_snap_reference(root, path);
        } else {
            std::string package_path;
            const std::string package = query_owner(root, path, package_path);
            const std::string deb_path = download_package(root, package, path);
            reference = extract_reference(root, deb_path, package_path, path);
        }

        try {
            const std::string expected = sha256_file(root, reference);
            const std::string actual = sha256_file(root, path);

            if (actual == expected) {
                std::cout << path << " : Success : Hash Match\n";
            }
            else {
                const auto reference_strings = extract_strings(reference);
                const auto actual_strings = extract_strings(path);
                const float score = score_string_overlap(reference_strings, actual_strings);

                std::cout << path << " : Check Required : String Comparison : " << score << "\n";
            }
        } catch (...) {
            unlink(reference.c_str());
            throw;
        }

        unlink(reference.c_str());
    } catch (const std::exception& error) {
        std::cerr << "UNRESOLVED " << path
                  << ": " << error.what() << '\n';
    }
}

// Prepare DNS and basic devices without invoking host executables.
static void prepare_downloads(const std::string& root)
{
    const fs::path disk_downloads =
        fs::path(root).parent_path() / "downloads";
    const std::string destination = root + "/downloads";

    fs::create_directories(disk_downloads);
    fs::create_directories(destination);

    // Inside the chroot, /downloads now refers to the disk directory.
    if (mount(disk_downloads.c_str(), destination.c_str(),
              nullptr, MS_BIND, nullptr) < 0) {
        fail("bind disk downloads");
    }

    // Remove any image symlink before writing resolv.conf.
    fs::remove(root + "/etc/resolv.conf");
    fs::copy_file("/etc/resolv.conf", root + "/etc/resolv.conf");

    fs::create_directories(root + "/dev");

    // A separate mount allows devices; the main rootfs remains nodev.
    if (mount("tmpfs", (root + "/dev").c_str(), "tmpfs",
              MS_NOSUID | MS_NOEXEC, "size=1M,mode=0755") < 0) {
        fail("mount private /dev");
    }

    for (const auto& device :
         std::vector<std::pair<const char*, unsigned int>>{
             {"null", 3}, {"zero", 5}, {"random", 8}, {"urandom", 9}
         }) {
        // Bind the kernel device by descriptor after checking its major/minor.
        const std::string path = std::string("/dev/") + device.first;
        const std::string target = root + path;
        const int placeholder = open(target.c_str(), O_CREAT | O_EXCL | O_WRONLY | O_CLOEXEC, 0600);
        if (placeholder < 0)
            fail("create " + target);
        close(placeholder);

        const int fd = open(path.c_str(), O_PATH | O_NOFOLLOW | O_CLOEXEC);
        if (fd < 0)
            fail("open " + path);

        try {
            struct stat info {};
            if (fstat(fd, &info) < 0)
                fail("fstat " + path);
            if (!S_ISCHR(info.st_mode) || info.st_rdev != makedev(1, device.second))
                throw std::runtime_error("Unexpected device at " + path);

            const std::string source = "/proc/self/fd/" + std::to_string(fd);
            if (mount(source.c_str(), target.c_str(), nullptr, MS_BIND, nullptr) < 0)
                fail("bind " + path);
        } catch (...) {
            close(fd);
            throw;
        }
        close(fd);
    }
}

int main()
{
    std::string root;
    int exit_code = 1;

    try {
        if (geteuid() != 0)
            throw std::runtime_error("Run as root (sudo)");

        // Find deb-rootfs.tar beside this executable.
        const fs::path executable = fs::read_symlink("/proc/self/exe");
        const fs::path tar_path =
            executable.parent_path() / "deb-rootfs.tar";

        // Create and populate the trusted environment.
        root = mount_rootfs();
        extract_rootfs(root, tar_path);

        // Expose the host database and prepare package downloads.
        expose_host_dpkg(root);
        prepare_downloads(root);

        std::cerr << "Bundled OS:\n"
                  << capture_command(
                         root, "/usr/bin/cat", {"/etc/os-release"}
                     );

        configure_ubuntu_mirror(root);
        refresh_repositories(root);

        // Show the configured repositories and the available libinput build.
        std::vector<std::string> args = apt_options();
        args.push_back("policy");
        run_in_rootfs(root, "/usr/bin/apt-cache", args);
        args.push_back("libinput10");
        run_in_rootfs(root, "/usr/bin/apt-cache", args);

        // Scan the host filesystem. Each detected ELF goes to check_elf().
        std::set<std::pair<dev_t, ino_t>> visited;
        // Prefer the canonical Snap path if a revision is also bind-mounted elsewhere.
        if (fs::is_directory(fs::symlink_status("/snap")))
            scan_directory(root, "/snap", visited);
        scan_directory(root, "/", visited);

        exit_code = 0;
    }
    catch (const std::exception& error) {
        std::cerr << "error: " << error.what() << '\n';
    }

    // Also runs after an exception; an empty root is handled safely.
    unmount_rootfs(root);

    return exit_code;
}
