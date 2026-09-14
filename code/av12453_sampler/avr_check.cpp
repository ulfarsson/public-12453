// avr_check.cpp -- C++ reader for AVR1 files, used to cross-check the C++ and
// Python indexing (avr_table.hpp vs avr_table.py) and to spot-print entries.
//
//   ./avr_check FILE --info
//   ./avr_check FILE --G p,q ... --R l,a,q,s ...
//   ./avr_check FILE --probe SEED COUNT     # deterministic pseudorandom probes:
//                                           # prints "R l a q s value" lines and
//                                           # "G p q value" lines
//   ./avr_check FILE --terms A:B
#include "avr_table.hpp"
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s FILE [--info] [--G p,q] [--R l,a,q,s] [--probe SEED COUNT] [--terms A:B]\n", argv[0]); return 2; }
    avr::Table T;
    std::string err = T.load(argv[1]);
    if (!err.empty()) { fprintf(stderr, "error: %s\n", err.c_str()); return 1; }
    bool did = false;
    for (int i = 2; i < argc; ++i) {
        std::string s = argv[i];
        if (s == "--info") {
            did = true;
            printf("N %d\nGentries %zu\nRrows %zu\nRentries %zu\nbytes %zu\naN %.17g\n",
                   T.N(), T.L.Gtotal, T.L.nrows, T.L.Rtotal,
                   (size_t)8 + 8 * (T.L.Gtotal + T.L.Rtotal), T.G(T.N(), 0));
        } else if (s == "--G" && i + 1 < argc) {
            did = true;
            int p, q; sscanf(argv[++i], "%d,%d", &p, &q);
            printf("G %d %d %.17g\n", p, q, T.G(p, q));
        } else if (s == "--R" && i + 1 < argc) {
            did = true;
            int l, a, q, ss; sscanf(argv[++i], "%d,%d,%d,%d", &l, &a, &q, &ss);
            printf("R %d %d %d %d %.17g\n", l, a, q, ss, T.R(l, a, q, ss));
        } else if (s == "--terms" && i + 1 < argc) {
            did = true;
            int A, B; sscanf(argv[++i], "%d:%d", &A, &B);
            for (int n = A; n <= B && n <= T.N(); ++n) printf("%d %.17g\n", n, T.G(n, 0));
        } else if (s == "--probe" && i + 2 < argc) {
            did = true;
            // xorshift64*, so Python can reproduce exactly the same probe list
            unsigned long long st = strtoull(argv[++i], nullptr, 10);
            long count = strtol(argv[++i], nullptr, 10);
            const int N = T.N();
            auto nxt = [&]() {
                st ^= st >> 12; st ^= st << 25; st ^= st >> 27;
                return (unsigned long long)(st * 2685821657736338717ULL);
            };
            for (long k = 0; k < count; ++k) {
                int l = 1 + (int)(nxt() % (unsigned)N);
                int a = (int)(nxt() % (unsigned)(N - l + 1));
                int q = (int)(nxt() % (unsigned)(N - l - a + 1));
                int ss = (int)(nxt() % (unsigned)avr::Layout::slen(a, q));
                printf("R %d %d %d %d %.17g\n", l, a, q, ss, T.R(l, a, q, ss));
                int p = (int)(nxt() % (unsigned)(N + 1));
                int qq = (int)(nxt() % (unsigned)(N - p + 1));
                printf("G %d %d %.17g\n", p, qq, T.G(p, qq));
            }
        } else { fprintf(stderr, "unknown option %s\n", s.c_str()); return 2; }
    }
    if (!did) printf("N %d\n", T.N());
    return 0;
}
