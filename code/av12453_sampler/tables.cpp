// tables.cpp -- double-precision reduced kernel table R and empty-stack table G
// for Av(12453), written in the "AVR1" (unscaled) or "AVR2" (power-of-two
// scaled) binary format.
//
// Mathematics: paper/av12453_polytime.tex, Sections 5 and 7, as restated in
// SAMPLER_BRIEF.md.  Everything is evaluated by the *direct* reduced
// recurrence in increasing reduced grade w = l+a+q; no evaluation/
// interpolation scheme is used (that is unstable in floating point).
//
//   slen(a,q) = q+1            if a = 0          (support {0..q})
//             = a+q            if a >= 1         (support {0..a+q-1})
//
//   R_{l,a}(q,s) = sum_{h=0}^{a-1} R_{l,h}(a+q-h-1,s)        [early band]
//                + sum_{r=0}^{q-1} R_{l+q-r-1,a}(r,s)        [last band]
//                + D_{l,a}(q,s)                              [endpoints]
//                + sum_{l1=1}^{l-2} sum_{a1=0}^{a} sum_m
//                     R_{l1,a1}(q,m) R_{l-1-l1,a-a1}(m,s)    [interior]
//   D_{1,a}(q,s) = [a=0][q=s],   D_{l,a}(q,s) = 2 R_{l-1,a}(q,s)  (l>=2)
//
//   G_{(0,0)} = 1;  for (p,q) != (0,0)
//   G_{(p,q)} = sum_{h=0}^{p-1} G_{(h,p+q-1-h)}
//             + sum_{h=0}^{q-1} [ delta=q-1-h == 0 ? G_{(p,h)}
//                               : sum_{a=0}^{p} sum_v R_{delta,a}(h,v) G_{(p-a,v)} ]
//   a_n = G_{(n,0)}.
//
// All summands are nonnegative, so there is no cancellation; the observed
// relative error against the exact terms is reported by check_terms.py.
//
// ---------------------------------------------------------------- scaling
// The counts at grade w reach about 2^{3.8 w}, so the unscaled table
// overflows binary64 beyond N ~ 260.  With --scaled the program stores
//
//     R'_{l,a}(q,s) = 2^{-2 w} R_{l,a}(q,s),   w = l+a+q   (grade)
//     G'_{(p,q)}    = 2^{-2 m} G_{(p,q)},      m = p+q     (mass)
//
// which lie in [2^{-2w}, 2^{1.8w}], inside the normal binary64 range for
// N <= 500.  The recurrence in the scaled variables is
//
//     early band : 2^{-2} R'_{l,h}(a+q-h-1,s)         (grade w-1)
//     last band  : 2^{-2} R'_{l+q-r-1,a}(r,s)         (grade w-1)
//     D          : l = 1 : 2^{-2w} [a=0][q=s];  l >= 2 : 2^{-2} * 2 R'_{l-1,a}(q,s)
//     split      : 4^{m-1} R'_{l1,a1}(q,m) R'_{l2,a2}(m,s)
//                  (w1 + w2 = w - 1 + m)
//     G early / zero block : 2^{-2} G'
//     G last band          : 4^{t-1} R'_{l,p-c}(r,t) G'_{(c,t)}
//
// The split factor 4^{m-1} must NOT be applied as (R' R') * 4^{m-1}: the two
// factors can each be as small as 2^{-2N}, so their product underflows to
// zero for large N (e.g. R_{l,0}(q,q) = C_l with q near 300).  It is applied
// in the *balanced* form (2^{m-1} R') * (2^{m-1} R'), where both factors stay
// in [2^{-2N-1}, 2^{2.8N}].  Two code paths implement it:
//   - fast path  : vv = v * 4^{m-1} is formed once per m (a whole A row at a
//                  time) and the inner loop stays a plain axpy
//                  `row[s] += vv*b[s]`, exactly as in the unscaled build.
//                  This is used whenever vv does not overflow; it is exact,
//                  because multiplying by a power of two is exact, and the
//                  final product vv*b[s] = 2^{-2w} R1 R2 is always in range.
//   - balanced   : otherwise `row[s] += (v*2^{m-1}) * (b[s]*2^{m-1})`.
// Both paths round identically (the power-of-two factors are exact and the
// mantissa product is the same), so the scaled table is bit-identical to the
// unscaled one after multiplication by 2^{2w}.  The program reports how often
// the balanced path is taken and the extreme magnitudes it stored.
//
// File format AVR1 (little-endian, as produced by the host):
//   int32 magic = 0x41565231 ('A','V','R','1' in that byte order)
//   int32 N
//   G: doubles, p = 0..N, q = 0..N-p                    (nested in that order)
//   R: doubles, l = 1..N, a = 0..N-l, q = 0..N-l-a, s = 0..slen(a,q)-1
// File format AVR2: magic 0x41565232, int32 N, int32 scale (= 2), then the
//   same two blocks holding the scaled entries.
//
// Build: see build_tables.sh.
// Usage: ./tables --N 150 --threads 4 --out N150.avr [--scaled]

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cmath>
#include <string>
#include <vector>
#include <algorithm>
#ifdef _OPENMP
#include <omp.h>
#endif
#include <ctime>
#include <sys/resource.h>


static double wall() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

#include "avr_table.hpp"
using avr::Layout;

// ------------------------------------------------------------------ kernels

static Layout L;
static double *Rd = nullptr;   // R data
static double *Gd = nullptr;   // G data
static double *GS = nullptr;   // scaled build only: GS[(c,t)] = G'_{(c,t)} * 2^{t-1}

// powers of two, exponents -2N-4 .. N+4 (exact, no ldexp in the hot loops)
static std::vector<double> POW2v;
static int POW2off = 0;
static inline double POW2(int e) { return POW2v[(size_t)(e + POW2off)]; }

// The fast split path is used while v*4^{m-1} stays comfortably finite.
// --force-balanced sets this to 0 so that every split takes the balanced path;
// the resulting table must be bit-identical (that is how the rarely-taken
// fallback is tested at an N where the fast path never overflows).
static double VVMAX = 1.0e300;

// per-thread scratch: the counters plus the buffer that holds one row of the
// split's A factor already multiplied by 4^{m-1}
struct Scratch {
    long long fast = 0, balanced = 0;
    std::vector<double> vbuf;   // A row of the split, pre-multiplied by 4^{m-1}
    std::vector<double> bbuf;   // B row of the split, pre-multiplied by 2^{m-1}
};

static inline const double *Rrow(int l, int a, int q) { return Rd + L.rrow(l, a, q); }
static inline double *RrowW(int l, int a, int q) { return Rd + L.rrow(l, a, q); }

template <bool SCALED>
static void computeRow(int l, int a, int q, Scratch &cnt) {
    const int n = Layout::slen(a, q);
    const int w = l + a + q;
    double *__restrict row = RrowW(l, a, q);
    for (int s = 0; s < n; ++s) row[s] = 0.0;

    // ---- early band: sum_{h=0}^{a-1} R_{l,h}(a+q-h-1, .)   (grade w-1)
    for (int h = 0; h < a; ++h) {
        const int qq = a + q - h - 1;
        const double *__restrict src = Rrow(l, h, qq);
        const int m = Layout::slen(h, qq);
        if (SCALED) { for (int s = 0; s < m; ++s) row[s] += 0.25 * src[s]; }
        else        { for (int s = 0; s < m; ++s) row[s] += src[s]; }
    }
    // ---- last band: sum_{r=0}^{q-1} R_{l+q-r-1,a}(r, .)    (grade w-1)
    for (int r = 0; r < q; ++r) {
        const double *__restrict src = Rrow(l + q - r - 1, a, r);
        const int m = Layout::slen(a, r);
        if (SCALED) { for (int s = 0; s < m; ++s) row[s] += 0.25 * src[s]; }
        else        { for (int s = 0; s < m; ++s) row[s] += src[s]; }
    }
    // ---- endpoint term D
    if (l == 1) {
        if (a == 0) row[q] += SCALED ? POW2(-2 * w) : 1.0;   // D_{1,0}(q,s) = [q=s]
    } else {
        const double *__restrict src = Rrow(l - 1, a, q);
        const double c = SCALED ? 0.5 : 2.0;                 // 2^{-2} * 2  vs  2
        for (int s = 0; s < n; ++s) row[s] += c * src[s];
    }
    // ---- interior split
    if (l >= 3) {
        double *__restrict vbuf = SCALED ? cnt.vbuf.data() : nullptr;
        for (int l1 = 1; l1 <= l - 2; ++l1) {
            const int l2 = l - 1 - l1;
            for (int a1 = 0; a1 <= a; ++a1) {
                const int a2 = a - a1;
                const double *__restrict row1 = Rrow(l1, a1, q);
                const int mm = Layout::slen(a1, q);
                if (SCALED) {
                    // Fold the whole factor 4^{m-1} into the A entry once per m
                    // (exact: a power of two).  The inner loop over s then stays
                    // the same plain axpy as in the unscaled build.  If that
                    // overflows -- only possible for a huge A entry paired with
                    // a large m -- mark the row with -1 and use the balanced
                    // form 2^{m-1} on each factor for that m alone.
                    for (int m = 0; m < mm; ++m) {
                        const double t = row1[m] * POW2(2 * m - 2);
                        vbuf[m] = (t <= VVMAX) ? t : -1.0;
                    }
                }
                const double *p2 = Rrow(l2, a2, 0);   // rows m = 0,1,2,... contiguous
                for (int m = 0; m < mm; ++m) {
                    const int n2 = Layout::slen(a2, m);
                    const double v = SCALED ? vbuf[m] : row1[m];
                    if (v > 0.0) {
                        const double *__restrict q2 = p2;
                        if (SCALED) ++cnt.fast;
                        for (int s = 0; s < n2; ++s) row[s] += v * q2[s];
                    } else if (SCALED && v < 0.0) {   // balanced fallback
                        ++cnt.balanced;
                        const double sc = POW2(m - 1);
                        const double v1 = row1[m] * sc;
                        const double *__restrict q2 = p2;
                        double *__restrict b = cnt.bbuf.data();
                        for (int s = 0; s < n2; ++s) b[s] = q2[s] * sc;
                        // same shape as the fast path, so the compiler emits the
                        // same (possibly fused) multiply-add and the result is
                        // bit-identical to the unscaled build
                        for (int s = 0; s < n2; ++s) row[s] += v1 * b[s];
                    }
                    p2 += n2;
                }
            }
        }
    }
}

// -------------------------------------------------------------- empty stack
template <bool SCALED>
static void computeG(int N) {
    for (int m = 0; m <= N; ++m) {
#pragma omp parallel for schedule(dynamic, 1)
        for (int p = 0; p <= m; ++p) {
            const int q = m - p;
            double tot = (m == 0) ? 1.0 : 0.0;      // G'_{(0,0)} = G_{(0,0)} = 1
            std::vector<double> rs(SCALED ? (size_t)N + 4 : (size_t)0, 0.0);
            for (int h = 0; h < p; ++h) {           // early band, mass m-1
                const double g = Gd[L.gindex(h, m - 1 - h)];
                tot += SCALED ? 0.25 * g : g;
            }
            for (int h = 0; h < q; ++h) {
                const int delta = q - 1 - h;
                if (delta == 0) {                   // K_0 = identity, mass m-1
                    const double g = Gd[L.gindex(p, h)];
                    tot += SCALED ? 0.25 * g : g;
                    continue;
                }
                for (int a = 0; a <= p; ++a) {
                    const double *__restrict rr = Rrow(delta, a, h);
                    const int nv = Layout::slen(a, h);
                    double acc = 0.0;
                    if (SCALED) {
                        // 4^{v-1} R'_{delta,a}(h,v) G'_{(p-a,v)} in balanced form:
                        // GS already carries the 2^{v-1} of the G factor, and the
                        // 2^{v-1} of the R factor is folded into a scratch row so
                        // that the dot product has exactly the same shape (and
                        // hence the same rounding, fused or not) as the unscaled
                        // one below.
                        const double *__restrict gs = GS + L.gindex(p - a, 0);
                        double *__restrict rsp = rs.data();
                        for (int v = 0; v < nv; ++v) rsp[v] = rr[v] * POW2(v - 1);
                        for (int v = 0; v < nv; ++v) acc += rsp[v] * gs[v];
                    } else {
                        const double *__restrict gu = Gd + L.gindex(p - a, 0);
                        for (int v = 0; v < nv; ++v) acc += rr[v] * gu[v];
                    }
                    tot += acc;
                }
            }
            Gd[L.gindex(p, q)] = tot;
        }
        if (SCALED)
            for (int p = 0; p <= m; ++p) {
                const size_t i = L.gindex(p, m - p);
                GS[i] = Gd[i] * POW2(m - p - 1);
            }
    }
}

int main(int argc, char **argv) {
    int N = 0, threads = 0, verbose = 0, scaled = 0;
    std::string out;
    for (int i = 1; i < argc; ++i) {
        std::string s = argv[i];
        auto need = [&](const char *what) -> const char * {
            if (i + 1 >= argc) { fprintf(stderr, "missing value for %s\n", what); exit(2); }
            return argv[++i];
        };
        if (s == "--N" || s == "-N") N = atoi(need("--N"));
        else if (s == "--threads" || s == "-t") threads = atoi(need("--threads"));
        else if (s == "--out" || s == "-o") out = need("--out");
        else if (s == "--scaled") scaled = 1;
        else if (s == "--force-balanced") VVMAX = 0.0;
        else if (s == "--verbose" || s == "-v") verbose = 1;
        else { fprintf(stderr, "usage: %s --N NUM [--threads T] [--out FILE] [--scaled]"
                       " [--force-balanced] [-v]\n", argv[0]); return 2; }
    }
    if (N < 1) { fprintf(stderr, "error: --N must be >= 1\n"); return 2; }
    if (N > 200 && !scaled)
        fprintf(stderr, "warning: N > 200 without --scaled; binary64 overflows beyond N ~ 260\n");
    if (N > 500 && scaled)
        fprintf(stderr, "warning: N > 500; the scaled entries may leave the normal range\n");
#ifdef _OPENMP
    if (threads > 0) omp_set_num_threads(threads);
    threads = omp_get_max_threads();
#else
    threads = 1;
#endif

    L.build(N);
    const size_t bytes = (L.Rtotal + L.Gtotal) * sizeof(double);
    fprintf(stderr, "N=%d threads=%d format=%s rows=%zu Rdoubles=%zu Gdoubles=%zu (%.1f MiB)\n",
            N, threads, scaled ? "AVR2 (scaled 2^{-2*grade})" : "AVR1 (unscaled)",
            L.nrows, L.Rtotal, L.Gtotal, bytes / 1048576.0);

    POW2off = 2 * N + 8;                       // exponents -2N-8 .. 2N+16
    POW2v.assign((size_t)(4 * N + 25), 0.0);
    for (int e = -POW2off; e + POW2off < (int)POW2v.size(); ++e)
        POW2v[(size_t)(e + POW2off)] = std::ldexp(1.0, e);
    long long tot_fast = 0, tot_bal = 0;

    Rd = (double *)calloc(L.Rtotal ? L.Rtotal : 1, sizeof(double));
    Gd = (double *)calloc(L.Gtotal, sizeof(double));
    if (scaled) GS = (double *)calloc(L.Gtotal, sizeof(double));
    if (!Rd || !Gd || (scaled && !GS)) { fprintf(stderr, "error: out of memory\n"); return 3; }

    // -------- kernel phase: increasing reduced grade w = l+a+q
    const double t0 = wall();
    // work list per grade: all (l,a) with l >= 1, a >= 0, l+a <= w
    std::vector<int> ls, as;
    for (int w = 1; w <= N; ++w) {
        ls.clear(); as.clear();
        for (int l = 1; l <= w; ++l)
            for (int a = 0; a <= w - l; ++a) { ls.push_back(l); as.push_back(a); }
        const long nr = (long)ls.size();
        // rows of one grade are mutually independent (all inputs have grade < w)
#pragma omp parallel
        {
            Scratch cnt;
            cnt.vbuf.assign((size_t)N + 4, 0.0);
            cnt.bbuf.assign((size_t)N + 4, 0.0);
#pragma omp for schedule(dynamic, 1)
            for (long i = 0; i < nr; ++i) {
                const int l = ls[i], a = as[i];
                if (scaled) computeRow<true>(l, a, w - l - a, cnt);
                else        computeRow<false>(l, a, w - l - a, cnt);
            }
#pragma omp critical
            { tot_fast += cnt.fast; tot_bal += cnt.balanced; }
        }
        if (verbose && (w % 10 == 0 || w == N))
            fprintf(stderr, "  grade %d/%d  %.2f s\n", w, N, wall() - t0);
    }
    const double tR = wall() - t0;
    fprintf(stderr, "kernel phase: %.3f s\n", tR);

    // -------- empty-stack phase
    const double t1 = wall();
    if (scaled) computeG<true>(N); else computeG<false>(N);
    const double tG = wall() - t1;
    fprintf(stderr, "empty-stack phase: %.3f s\n", tG);
    fprintf(stderr, "total build: %.3f s\n", tR + tG);
    {
        struct rusage ru;
        if (getrusage(RUSAGE_SELF, &ru) == 0)
            fprintf(stderr, "peak RSS: %.1f MiB\n", ru.ru_maxrss / 1024.0);
    }

    // -------- range audit: every stored entry must be finite and normal
    {
        double rmin = HUGE_VAL, rmax = 0.0, gmin = HUGE_VAL, gmax = 0.0;
        long long nonfinite = 0, subnormal = 0;
        const double TINY = 2.2250738585072014e-308;   // smallest normal double
#pragma omp parallel for schedule(static) \
        reduction(+:nonfinite,subnormal) reduction(min:rmin) reduction(max:rmax)
        for (size_t i = 0; i < L.Rtotal; ++i) {
            const double v = Rd[i];
            if (!std::isfinite(v)) { ++nonfinite; continue; }
            if (v == 0.0) continue;
            if (std::fabs(v) < TINY) ++subnormal;
            if (v < rmin) rmin = v;
            if (v > rmax) rmax = v;
        }
        for (size_t i = 0; i < L.Gtotal; ++i) {
            const double v = Gd[i];
            if (!std::isfinite(v)) { ++nonfinite; continue; }
            if (v == 0.0) continue;
            if (std::fabs(v) < TINY) ++subnormal;
            if (v < gmin) gmin = v;
            if (v > gmax) gmax = v;
        }
        fprintf(stderr, "R nonzero range: [%.6g, %.6g]  = [2^%.1f, 2^%.1f]\n",
                rmin, rmax, std::log2(rmin), std::log2(rmax));
        fprintf(stderr, "G nonzero range: [%.6g, %.6g]  = [2^%.1f, 2^%.1f]\n",
                gmin, gmax, std::log2(gmin), std::log2(gmax));
        fprintf(stderr, "non-finite entries: %lld   subnormal entries: %lld\n",
                nonfinite, subnormal);
        if (nonfinite) { fprintf(stderr, "ERROR: the table overflowed\n"); return 5; }
    }
    if (scaled)
        fprintf(stderr, "split inner loops: %lld fast (v*4^{m-1}), %lld balanced (%.3g%%)\n",
                tot_fast, tot_bal,
                100.0 * (double)tot_bal / (double)(tot_fast + tot_bal ? tot_fast + tot_bal : 1));
    {
        const double aN = Gd[L.gindex(N, 0)];
        fprintf(stderr, "a_%d = G_(%d,0) = %.17g", N, N, aN);
        if (scaled) fprintf(stderr, "  (scaled; true value = that * 2^%d ~ 10^%.2f)",
                            2 * N, std::log10(aN) + 2 * N * std::log10(2.0));
        fprintf(stderr, "\n");
    }

    // -------- write AVR1 / AVR2
    if (!out.empty()) {
        FILE *f = fopen(out.c_str(), "wb");
        if (!f) { perror("fopen"); return 4; }
        int32_t magic = scaled ? avr::AVR2_MAGIC : avr::AVR_MAGIC, n32 = N;
        int32_t sc = avr::AVR2_SCALE;
        if (fwrite(&magic, 4, 1, f) != 1 || fwrite(&n32, 4, 1, f) != 1) { perror("fwrite"); return 4; }
        if (scaled && fwrite(&sc, 4, 1, f) != 1) { perror("fwrite"); return 4; }
        if (fwrite(Gd, sizeof(double), L.Gtotal, f) != L.Gtotal) { perror("fwrite G"); return 4; }
        size_t done = 0;
        while (done < L.Rtotal) {                       // chunked for very large N
            size_t chunk = std::min<size_t>(1u << 22, L.Rtotal - done);
            if (fwrite(Rd + done, sizeof(double), chunk, f) != chunk) { perror("fwrite R"); return 4; }
            done += chunk;
        }
        if (fclose(f)) { perror("fclose"); return 4; }
        fprintf(stderr, "wrote %s (%zu bytes)\n", out.c_str(),
                avr::hdr_bytes(magic) + (L.Gtotal + L.Rtotal) * 8);
    }
    return 0;
}
