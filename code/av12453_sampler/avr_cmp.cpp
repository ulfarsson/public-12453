// avr_cmp.cpp -- bit-identity comparison of two AVR tables (AVR1 or AVR2).
//
//   ./avr_cmp A.avr B.avr [--top K] [--rel]
//
// Every stored entry of both tables is brought to the *unscaled* footing by
// multiplying by 2^{scale*grade} (scale = 0 for AVR1, 2 for AVR2), and the
// two binary64 values are compared BIT BY BIT.  Because multiplication by a
// power of two is exact, an AVR2 table built by the same code path as an AVR1
// table must agree bit for bit wherever the unscaled value is representable.
//
// The comparison is done on the common support, grade <= min(N_A, N_B), so
// the tool doubles as the N-independence (prefix) check.
//
// With --rel the comparison is by rescaled ratio instead of by bits, which
// keeps working when the unscaled value overflows binary64 (then only the
// scaled table is meaningful and the tool reports the overflow count).
#include "avr_table.hpp"
#include <cstdio>
#include <cstring>
#include <cmath>
#include <string>
#include <vector>
#include <algorithm>

static bool same_bits(double x, double y) {
    return std::memcmp(&x, &y, sizeof(double)) == 0;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s A.avr B.avr [--top K] [--rel]\n", argv[0]);
        return 2;
    }
    int top = 5; bool rel_mode = false;
    for (int i = 3; i < argc; ++i) {
        const std::string s = argv[i];
        if (s == "--top" && i + 1 < argc) top = atoi(argv[++i]);
        else if (s == "--rel") rel_mode = true;
        else { fprintf(stderr, "unknown option %s\n", s.c_str()); return 2; }
    }
    avr::Table A, B;
    std::string e = A.load(argv[1]); if (!e.empty()) { fprintf(stderr, "error: %s\n", e.c_str()); return 1; }
    e = B.load(argv[2]);             if (!e.empty()) { fprintf(stderr, "error: %s\n", e.c_str()); return 1; }
    const int N = std::min(A.N(), B.N());
    printf("A %s  N=%d scale=%d (%s)\n", argv[1], A.N(), A.scale, A.scaled() ? "AVR2" : "AVR1");
    printf("B %s  N=%d scale=%d (%s)\n", argv[2], B.N(), B.scale, B.scaled() ? "AVR2" : "AVR1");
    printf("comparing the common support, grade <= %d\n", N);

    long long nR = 0, nG = 0, badR = 0, badG = 0, ovf = 0, zeroboth = 0;
    double maxrel = 0.0;
    int wl = 0, wa = 0, wq = 0, ws = 0;
    std::vector<std::string> worst;

    for (int l = 1; l <= N; ++l)
        for (int a = 0; a <= N - l; ++a)
            for (int q = 0; q <= N - l - a; ++q) {
                const int w = l + a + q;
                const int n = avr::Layout::slen(a, q);
                const double *ra = A.R_.data() + A.L.rrow(l, a, q);
                const double *rb = B.R_.data() + B.L.rrow(l, a, q);
                for (int s = 0; s < n; ++s) {
                    const double xa = std::ldexp(ra[s], A.scale * w);
                    const double xb = std::ldexp(rb[s], B.scale * w);
                    ++nR;
                    if (!std::isfinite(xa) || !std::isfinite(xb)) { ++ovf; continue; }
                    if (xa == 0.0 && xb == 0.0) { ++zeroboth; continue; }
                    const bool ok = rel_mode ? (std::fabs(xa - xb) <= 0.0) : same_bits(xa, xb);
                    if (!ok) {
                        ++badR;
                        const double d = xb != 0.0 ? std::fabs(xa - xb) / std::fabs(xb) : 1.0;
                        if (d > maxrel) { maxrel = d; wl = l; wa = a; wq = q; ws = s; }
                        if ((int)worst.size() < top) {
                            char buf[256];
                            snprintf(buf, sizeof buf, "  R(%d,%d,%d,%d): A=%.17g B=%.17g rel=%.3e",
                                     l, a, q, s, xa, xb, d);
                            worst.push_back(buf);
                        }
                    }
                }
            }
    for (int p = 0; p <= N; ++p)
        for (int q = 0; q <= N - p; ++q) {
            const int m = p + q;
            const double xa = std::ldexp(A.G(p, q), A.scale * m);
            const double xb = std::ldexp(B.G(p, q), B.scale * m);
            ++nG;
            if (!std::isfinite(xa) || !std::isfinite(xb)) { ++ovf; continue; }
            if (!same_bits(xa, xb)) {
                ++badG;
                if ((int)worst.size() < top) {
                    char buf[256];
                    snprintf(buf, sizeof buf, "  G(%d,%d): A=%.17g B=%.17g", p, q, xa, xb);
                    worst.push_back(buf);
                }
            }
        }
    printf("R entries compared %lld   mismatches %lld   (both zero: %lld)\n", nR, badR, zeroboth);
    printf("G entries compared %lld   mismatches %lld\n", nG, badG);
    printf("entries skipped because the unscaled value overflows binary64: %lld\n", ovf);
    if (badR) printf("worst R relative difference %.6e at (l,a,q,s)=(%d,%d,%d,%d)\n",
                     maxrel, wl, wa, wq, ws);
    for (const std::string &s : worst) printf("%s\n", s.c_str());
    printf("verdict %s\n", (badR == 0 && badG == 0) ? "PASS (bit-identical)" : "FAIL");
    return (badR == 0 && badG == 0) ? 0 : 1;
}
