#include <cerrno>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <string>

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

extern char **environ;

extern "C" {
    // These come from linker-produced binary blobs.
    extern const unsigned char _binary_nix_locate_start[];
    extern const unsigned char _binary_nix_locate_end[];

    extern const unsigned char _binary_nix_index_start[];
    extern const unsigned char _binary_nix_index_end[];
}

static void write_all(int fd, const unsigned char* data, size_t size)
{
    while (size > 0) {
        ssize_t n = write(fd, data, size);

        if (n < 0) {
            if (errno == EINTR)
                continue;

            throw std::runtime_error(
                std::string("write: ") + strerror(errno)
            );
        }

        data += n;
        size -= n;
    }

    lseek(fd, 0, SEEK_SET);
}

static int blob_to_memfd(
    const char* name,
    const unsigned char* start,
    const unsigned char* end)
{
    // Intentionally NO MFD_CLOEXEC:
    // the database fd must survive exec().
    int fd = memfd_create(name, 0);

    if (fd == -1)
        throw std::runtime_error(
            std::string("memfd_create: ") + strerror(errno)
        );

    write_all(
        fd,
        start,
        static_cast<size_t>(end - start)
    );

    return fd;
}

// Turn:
//     libm.so.6
//
// into:
//     libm\.so\.6
//
// because nix-locate patterns are regexes.
static std::string regex_escape(const std::string& s)
{
    const std::string special = R"(\.^$|()[]{}*+?)";

    std::string out;

    for (char c : s) {
        if (special.find(c) != std::string::npos)
            out += '\\';

        out += c;
    }

    return out;
}

int main()
{
    try {
        std::string filename;

        std::cout << "ELF filename: ";
        std::getline(std::cin, filename);

        /*
         * 1. Materialize the two embedded blobs into anonymous
         *    memory-backed file descriptors.
         */
        int locate_fd = blob_to_memfd(
            "embedded-nix-locate",
            _binary_nix_locate_start,
            _binary_nix_locate_end
        );

        int db_fd = blob_to_memfd(
            "embedded-nix-index",
            _binary_nix_index_start,
            _binary_nix_index_end
        );

        std::string locate_path =
            "/proc/self/fd/" + std::to_string(locate_fd);

        std::string db_path =
            "/proc/self/fd/" + std::to_string(db_fd);

        /*
         * 2. nix-locate's --db expects:
         *
         *       DB_DIRECTORY/files
         *
         * We therefore make a tiny RAM-backed directory and make
         * "files" refer to our database memfd.
         */
        char dir_template[] =
            "/dev/shm/nixlocate-XXXXXX";

        char* db_dir_raw = mkdtemp(dir_template);

        if (!db_dir_raw)
            throw std::runtime_error(
                std::string("mkdtemp: ") + strerror(errno)
            );

        std::string db_dir = db_dir_raw;
        std::string files_path = db_dir + "/files";

        if (symlink(db_path.c_str(), files_path.c_str()) == -1)
            throw std::runtime_error(
                std::string("symlink: ") + strerror(errno)
            );

        /*
         * Search for a file with exactly this basename.
         *
         * libm.so.6 becomes:
         *
         *     (^|/)libm\.so\.6$
         */
        std::string pattern =
            "(^|/)" + regex_escape(filename) + "$";

        /*
         * 3. Pipe allows us to capture nix-locate's stdout.
         */
        int output[2];

        if (pipe(output) == -1)
            throw std::runtime_error("pipe failed");

        pid_t pid = fork();

        if (pid == -1)
            throw std::runtime_error("fork failed");

        if (pid == 0) {
            /*
             * CHILD
             */

            close(output[0]);

            dup2(output[1], STDOUT_FILENO);
            close(output[1]);

            /*
             * Equivalent to:
             *
             * nix-locate
             *     --db /dev/shm/nixlocate-XXXXXX
             *     '(^|/)libm\.so\.6$'
             */
            char* argv[] = {
                const_cast<char*>("nix-locate"),
                const_cast<char*>("--db"),
                const_cast<char*>(db_dir.c_str()),
                const_cast<char*>(pattern.c_str()),
                nullptr
            };

            /*
             * Execute the embedded ELF through procfs.
             */
            execve(
                locate_path.c_str(),
                argv,
                environ
            );

            perror("execve");
            _exit(127);
        }

        /*
         * PARENT
         */
        close(output[1]);

        char buf[4096];

        while (true) {
            ssize_t n = read(output[0], buf, sizeof(buf));

            if (n <= 0)
                break;

            std::cout.write(buf, n);
        }

        close(output[0]);

        int status;
        waitpid(pid, &status, 0);

        /*
         * Remove the tiny directory metadata.
         * Closing the memfds destroys the anonymous objects.
         */
        unlink(files_path.c_str());
        rmdir(db_dir.c_str());

        close(db_fd);
        close(locate_fd);

        return WIFEXITED(status)
            ? WEXITSTATUS(status)
            : 1;
    }
    catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << '\n';
        return 1;
    }
}
