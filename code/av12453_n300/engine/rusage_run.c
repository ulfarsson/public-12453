/* rusage_run.c -- minimal /usr/bin/time replacement: fork+exec a command, wait4,
   report wall clock and the child's peak RSS on stderr, and forward its exit code. */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <time.h>
#include <sys/wait.h>
#include <sys/resource.h>
int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: rusage_run CMD [ARGS...]\n"); return 2; }
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    pid_t pid = fork();
    if (pid < 0) { perror("fork"); return 2; }
    if (pid == 0) { execvp(argv[1], argv + 1); perror("execvp"); _exit(127); }
    int status = 0; struct rusage ru;
    if (wait4(pid, &status, 0, &ru) < 0) { perror("wait4"); return 2; }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double wall = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
    fprintf(stderr, "RUSAGE wall_s=%.3f maxrss_kib=%ld maxrss_mib=%.2f user_s=%.3f sys_s=%.3f\n",
            wall, ru.ru_maxrss, ru.ru_maxrss / 1024.0,
            ru.ru_utime.tv_sec + 1e-6 * ru.ru_utime.tv_usec,
            ru.ru_stime.tv_sec + 1e-6 * ru.ru_stime.tv_usec);
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    return 128 + WTERMSIG(status);
}
