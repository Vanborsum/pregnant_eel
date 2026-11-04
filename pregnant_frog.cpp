// Build with default.nix. Run as root with rpm-rootfs.tar beside the executable.
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
static const char* package_format =
    "%{NAME}.%{ARCH}=%{EPOCHNUM}:%{VERSION}-%{RELEASE}\n";

static void prepare_downloads(const std::string& root);
static void check_elf(
    const std::string& root,
    const std::string& path);
static std::string sha256_file(
    const std::string& root,
    const std::string& path);
static std::vector<std::string> extract_strings(const std::string& path);
static std::string extract_reference(
    const std::string& root,
    const std::string& rpm_path,
    const std::string& elf_path);
static std::string download_package(
    const std::string& root,
    const std::string& package,
    const std::string& path);
static void scan_directory(
    const std::string& root,
    const fs::path& directory,
    std::set<std::pair<dev_t, ino_t>>& visited);
static void expose_host_rpmdb(
    const std::string& root,
    std::string database_path = "");
static std::string query_owner(
    const std::string& root,
    const std::string& path);
static std::string one_package(const std::string& text);
static std::string one_package(const std::string& text, const std::string& path);
static std::string capture_command(
    const std::string& root,
    const char* program,
    const std::vector<std::string>& args,
    int input_fd = -1);
static int run_zypper(const std::string& root, const std::vector<std::string>& args);
static int run_rpm(const std::string& root, const std::vector<std::string>& args);
static int run_in_rootfs(
    const std::string& root,
    const char* program,
    std::vector<std::string> args,
    int output_fd = -1,
    int input_fd = -1);
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
    //remove calling process from inherited namespace
    if (unshare(CLONE_NEWNS) < 0)
        fail("unshare (requires CAP_SYS_ADMIN)");

    //Make mounts private (dont alert upwards about mounts in the tempfs)
    if (mount(nullptr, "/", nullptr, MS_REC | MS_PRIVATE, nullptr) < 0)
        fail("make mounts private");

    char parent[] = "/var/tmp/rpm-env-XXXXXX";
    if (!mkdtemp(parent))
        fail("mkdtemp");

    // make a root directory for the in-memory openSUSE
    const std::string root = std::string(parent) + "/root";

    try {
        if (mkdir(root.c_str(), 0700) < 0)
            fail("mkdir mountpoint");

        // Allow execution; ignore setuid bits and device nodes. Limit: 512 MiB.
        if (mount("tmpfs", root.c_str(), "tmpfs", MS_NOSUID | MS_NODEV,
                  "size=512M,mode=0755") < 0) {
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
    int input_fd)
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

        if (chroot(root.c_str()) < 0 || chdir("/") < 0) {
            std::perror("enter rootfs");
            _exit(127);
        }

        execve(program, argv.data(), envp);
        std::perror("execve");
        _exit(127);
    }

    return wait_for(pid);
}

// Call the bundled rpm, for example: run_rpm(root, {"--version"}).
static int run_rpm(const std::string& root, const std::vector<std::string>& args)
{
    return run_in_rootfs(root, "/usr/bin/rpm", args);
}

// Call the bundled zypper, for example: run_zypper(root, {"--version"}).
static int run_zypper(const std::string& root, const std::vector<std::string>& args)
{
    return run_in_rootfs(root, "/usr/bin/zypper", args);
}

// Run a bundled command and return stdout. Throw if the command fails.
// Stderr remains connected to the terminal.
static std::string capture_command(
    const std::string& root,
    const char* program,
    const std::vector<std::string>& args,
    int input_fd)
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

        if (status != 0) {
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

// Return the first package reported by RPM.
static std::string one_package(const std::string& text)
{
    std::istringstream lines(text);
    std::string package;

    if (!std::getline(lines, package) || package.empty())
        throw std::runtime_error("No package identity returned");

    return package;
}

// Return the first package reported by RPM.
static std::string one_package(const std::string& text, const std::string& path)
{
    std::istringstream lines(text);
    std::string package;

    if (!std::getline(lines, package) || package.empty())
    {
        std::cout << path << " : Failure : No Corresponding Package Identified\n";
        throw std::runtime_error("No package identity returned");
    }

    return package;
}

// Query the host database and return an exact Zypper package selector.
static std::string query_owner(
    const std::string& root,
    const std::string& path)
{
    return one_package(capture_command(root, "/usr/bin/rpm", {
        "--dbpath", "/host-rpmdb",
        "-q", "--path", path,
        "--qf", package_format
    }), path);
}

// Expose the host's RPM database inside the bundled environment.
// Call once after extracting the rootfs.
// An explicit database_path overrides automatic path detection.
static void expose_host_rpmdb(
    const std::string& root,
    std::string database_path)
{
    //determine which of the 2 canonical paths are being used to store the rpm database
    if (database_path.empty()) {
        for (const char* candidate : {
                 "/usr/lib/sysimage/rpm",
                 "/var/lib/rpm"
             }) {
            if (fs::is_directory(candidate)) {
                database_path = candidate;
                break;
            }
        }
    }

    if (database_path.empty())
        throw std::runtime_error("Cannot find the host RPM database");

    // Resolve aliases such as /var/lib/rpm -> /usr/lib/sysimage/rpm.
    const std::string source = fs::canonical(database_path).string();
    const std::string destination = root + "/host-rpmdb";

    if (mkdir(destination.c_str(), 0700) < 0)
        fail("mkdir host-rpmdb");

    if (mount(source.c_str(), destination.c_str(),
              nullptr, MS_BIND, nullptr) < 0) {
        fail("bind mount RPM database");
    }

    // A bind mount needs a separate remount to make this view read-only.
    const unsigned long flags =
        MS_BIND | MS_REMOUNT | MS_RDONLY |
        MS_NOSUID | MS_NODEV | MS_NOEXEC;

    if (mount(nullptr, destination.c_str(), nullptr, flags, nullptr) < 0) {
        const int error = errno;
        umount2(destination.c_str(), MNT_DETACH);
        errno = error;
        fail("make RPM database mount read-only");
    }
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

// Download and check the exact package. Return its path INSIDE the chroot.
// Uses the bundled environment's repositories and trusted keys.
static std::string download_package(
    const std::string& root,
    const std::string& package,
    const std::string& path)
{
    static std::map<std::string, std::string> cache;

    const std::string key = root + "\n" + package;
    if (cache.count(key))
        return cache.at(key);

    fs::create_directories(root + "/downloads");

    std::string directory = root + "/downloads/package-XXXXXX";
    if (!mkdtemp(directory.data()))
        fail("mkdtemp download");

    const std::string inside =
        "/downloads/" + fs::path(directory).filename().string();

    int status = run_zypper(root, {
        "--non-interactive",
        "--pkg-cache-dir", inside,
        "download", "--", package
    });

    if (status != 0)
    {
        std::cout << path << " : Failure : Corresponding Package Failed to Download\n";
        throw std::runtime_error("Exact package download failed: " + package);
    }

    std::string found;

    for (const auto& entry : fs::recursive_directory_iterator(directory)) {
        if (!entry.is_regular_file() || entry.path().extension() != ".rpm")
            continue;

        const std::string rpm_path =
            "/" + entry.path().lexically_relative(root).generic_string();

        // Check the downloaded RPM using the image's key database.
        capture_command(root, "/usr/bin/rpmkeys", {
            "--checksig", rpm_path
        });

        // Confirm Zypper returned precisely the requested package identity.
        const std::string actual = one_package(
            capture_command(root, "/usr/bin/rpm", {
                "-qp", "--qf", package_format, rpm_path
            })
        );

        if (actual != package)
            throw std::runtime_error(
                    "Downloaded package identity does not match: requested [" +
                    package + "], received [" + actual + "]"
                );

        if (!found.empty())
            throw std::runtime_error("More than one reference RPM downloaded");

        found = rpm_path;
    }

    if (found.empty())
        throw std::runtime_error("No downloaded RPM found");

    cache[key] = found;
    return found;
}

// Extract one file from a downloaded RPM into our tmpfs.
//
// rpm_path: path INSIDE the chroot, e.g. /downloads/.../package.rpm.
// elf_path: original HOST path, e.g. /usr/bin/foo.
//
// Returns a parent-visible temporary filename. Caller must unlink it.
static std::string extract_reference(
    const std::string& root,
    const std::string& rpm_path,
    const std::string& elf_path)
{
    const std::string package_file = root + rpm_path;

    const std::string wanted =
        fs::path(elf_path).lexically_normal().relative_path().generic_string();

    fs::create_directories(root + "/reference");

    archive* reader = nullptr;
    int output_fd = -1;
    std::string output_path;

    dev_t device = 0;
    la_int64_t inode = 0;
    bool found = false;
    bool hardlinked = false;

    try {
        // Pass 1 finds the target's identity.
        // Pass 2 finds its contents, which may belong to another hardlink entry.
        for (int pass = 0; pass < 2; ++pass) {
            reader = archive_read_new();

            if (!reader)
                throw std::runtime_error("Cannot allocate RPM reader");

            check_archive(archive_read_support_filter_rpm(reader), reader);
            check_archive(archive_read_support_filter_gzip(reader), reader);
            check_archive(archive_read_support_filter_bzip2(reader), reader);
            check_archive(archive_read_support_filter_xz(reader), reader);
            check_archive(archive_read_support_filter_zstd(reader), reader);
            check_archive(archive_read_support_format_cpio(reader), reader);

            check_archive(
                archive_read_open_filename(
                    reader, package_file.c_str(), 1024 * 1024
                ),
                reader
            );

            archive_entry* entry;
            int status;

            while ((status = archive_read_next_header(reader, &entry))
                   != ARCHIVE_EOF) {
                check_archive(status, reader);

                const char* name = archive_entry_pathname(entry);

                if (!name)
                    throw std::runtime_error("RPM entry has no pathname");

                // Normalize "./usr/bin/foo" and "/usr/bin/foo" for comparison.
                const std::string entry_path =
                    fs::path(name).lexically_normal()
                                  .relative_path().generic_string();

                if (pass == 0) {
                    if (entry_path != wanted)
                        continue;

                    if (archive_entry_filetype(entry) != AE_IFREG)
                        throw std::runtime_error(
                            "Reference is not a regular file"
                        );

                    device = archive_entry_dev(entry);
                    inode = archive_entry_ino64(entry);
                    hardlinked = archive_entry_nlink(entry) > 1;
                    found = true;
                    break;
                }

                if (archive_entry_filetype(entry) != AE_IFREG)
                    continue;

                if (hardlinked) {
                    // Find the entry carrying this hardlink group's bytes.
                    if (archive_entry_dev(entry) != device ||
                        archive_entry_ino64(entry) != inode ||
                        archive_entry_size(entry) == 0) {
                        continue;
                    }
                }
                else if (entry_path != wanted) {
                    continue;
                }

                output_path = root + "/reference/elf-XXXXXX";
                output_fd = mkstemp(output_path.data());

                if (output_fd < 0)
                    fail("mkstemp reference");

                // Copy bytes to our chosen filename. No archive paths or
                // symlinks are created, and no installation scripts are run.
                check_archive(
                    archive_read_data_into_fd(reader, output_fd),
                    reader
                );

                int close_status = close(output_fd);
                output_fd = -1;

                if (close_status < 0)
                    fail("close reference");

                archive_read_free(reader);
                reader = nullptr;

                return output_path;
            }

            archive_read_free(reader);
            reader = nullptr;

            if (!found)
            {
                std::cout << elf_path << " : Failure : Binary Could Not be Parsed From rpm Archive\n";
                throw std::runtime_error(
                    "ELF path is absent from the RPM payload"
                );
            }
        }

        throw std::runtime_error(
            "No data-bearing entry found for reference hardlink"
        );
    }
    catch (...) {
        if (reader)
            archive_read_free(reader);

        if (output_fd >= 0)
            close(output_fd);

        if (!output_path.empty())
            unlink(output_path.c_str());

        throw;
    }
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

static float score_string_overlap(
    std::vector<std::string>& reference_strings,
    std::vector<std::string>& actual_strings)
{
    if (reference_strings.empty())
        return 0.0f;
    if (actual_strings.empty())
        return 0.0f;

    float first_percentage = 0.0;
    float second_percentage = 0.0;
    float numerator = 0.0;
    float denominator = 0.0;

    for (std::string s : reference_strings)
    {
        int found = 0;
        for (std::string candidate : actual_strings)
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

    for (std::string s : actual_strings)
    {
        int found = 0;
        for (std::string candidate : reference_strings)
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

// Look up, download, and compare one detected ELF.
// A failed lookup/download is unresolved, not a hash mismatch.
static void check_elf(
    const std::string& root,
    const std::string& path)
{
    try {
        const std::string package = query_owner(root, path);
        const std::string rpm_path = download_package(root, package, path);
        const std::string reference = extract_reference(root, rpm_path, path);
        std::string expected;

        try {
            expected = sha256_file(root, reference);
        }
        catch (...) {
            unlink(reference.c_str());
            throw;
        }

        const std::string actual = sha256_file(root, path);

        if (actual == expected)
        {
            std::cout << path << " : Success : Hash Match\n";
        }
        else
        {
            std::vector<std::string> reference_strings = extract_strings(reference);
            std::vector<std::string> actual_strings = extract_strings(path);

            float score = score_string_overlap(reference_strings, actual_strings);

            std::cout << path << " : Check Required : String Comparison : " << score << "\n";
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
        const std::string path = root + "/dev/" + device.first;

        if (mknod(path.c_str(), S_IFCHR | 0666,
                  makedev(1, device.second)) < 0) {
            fail("mknod " + path);
        }
    }
}

int main()
{
    std::string root;
    int exit_code = 1;

    try {
        if (geteuid() != 0)
            throw std::runtime_error("Run as root (sudo)");

        // Find rpm-rootfs.tar beside this executable.
        const fs::path executable = fs::read_symlink("/proc/self/exe");
        const fs::path tar_path =
            executable.parent_path() / "rpm-rootfs.tar";

        // Create and populate the trusted environment.
        root = mount_rootfs();
        extract_rootfs(root, tar_path);

        // Expose the host database and prepare package downloads.
        expose_host_rpmdb(root);
        prepare_downloads(root);

        std::cerr << "Bundled OS:\n"
                  << capture_command(
                         root, "/usr/bin/cat", {"/etc/os-release"}
                     );

        run_zypper(root, {"repos", "--uri"});

        run_zypper(root, {
            "search", "--details", "--match-exact", "libinput-udev"
        });

        // Scan the host filesystem. Each detected ELF goes to check_elf().
        std::set<std::pair<dev_t, ino_t>> visited;
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
