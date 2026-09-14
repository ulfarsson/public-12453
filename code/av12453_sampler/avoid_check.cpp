// avoid_check.cpp -- standalone independent avoidance checker.
//   avoid_check FILE...          reads permutations (one per line, values 1..n)
//   avoid_check --brute FILE...  also runs the naive O(n^5) test and compares
// Exits 1 if any line contains 12453 (or the two tests disagree).
#include "avoid12453.hpp"
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

int main(int argc, char **argv) {
    bool brute = false;
    std::vector<const char *> files;
    for (int i = 1; i < argc; ++i) {
        if (!std::strcmp(argv[i], "--brute")) brute = true;
        else files.push_back(argv[i]);
    }
    if (files.empty()) { std::fprintf(stderr, "usage: avoid_check [--brute] FILE...\n"); return 2; }
    long long total = 0, bad = 0, disagree = 0;
    av::Scratch sc;
    std::vector<int> perm;
    std::vector<char> seen;
    std::string line;
    for (const char *f : files) {
        FILE *fp = std::strcmp(f, "-") ? std::fopen(f, "rb") : stdin;
        if (!fp) { std::fprintf(stderr, "cannot open %s\n", f); return 2; }
        char *buf = nullptr; size_t cap = 0; ssize_t len;
        long long lineno = 0;
        while ((len = getline(&buf, &cap, fp)) > 0) {
            ++lineno;
            perm.clear();
            for (char *p = buf; *p; ) {
                while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r') ++p;
                if (!*p) break;
                perm.push_back((int)std::strtol(p, &p, 10));
            }
            if (perm.empty()) continue;
            const int n = (int)perm.size();
            seen.assign((size_t)n + 1, 0);
            for (int v : perm) {
                if (v < 1 || v > n || seen[(size_t)v]) {
                    std::fprintf(stderr, "%s:%lld: not a permutation of 1..%d\n", f, lineno, n);
                    return 1;
                }
                seen[(size_t)v] = 1;
            }
            ++total;
            const bool c1 = av::contains_12453(perm.data(), n, sc);
            if (c1) { ++bad; if (bad <= 3) std::fprintf(stderr, "%s:%lld contains 12453\n", f, lineno); }
            if (brute) {
                const bool c2 = av::brute_contains_12453(perm.data(), n);
                if (c1 != c2) { ++disagree;
                    std::fprintf(stderr, "%s:%lld DISAGREE trigger=%d brute=%d\n", f, lineno, (int)c1, (int)c2); }
            }
        }
        std::free(buf);
        if (fp != stdin) std::fclose(fp);
    }
    std::printf("checked %lld permutations: %lld contain 12453%s\n", total, bad,
                brute ? (disagree ? "  (BRUTE DISAGREES)" : "  (brute-force agrees on all)") : "");
    return (bad || disagree) ? 1 : 0;
}
