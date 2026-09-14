// av12453_gemm_split.cpp -- GEMM realization of the homogeneous split scheme for
// the reduced d=2 protected-tail kernel recurrence of Av(12453).
//
// Derived from repo/code/av12453_homog_split.cpp (bands, D term, absorption into E,
// inverse-Vandermonde interpolation, empty-stack phase, CERTIFY, support check,
// --dump-r, instrumented counters are kept verbatim in substance).  The only part
// that is rewritten is the split kernel, which is now a dense matrix product.
//
//   R[l][a][q][s] = sum_{h<a} R[l][h][a+q-h-1][s]              (BAND1)
//                 + sum_{r<q} R[l+q-r-1][a][r][s]              (BAND2)
//                 + (l==1 ? [a==0 && q==s] : 2 R[l-1][a][q][s]) (D)
//                 + SPLIT[l][a][q][s],
//   SPLIT = sum_{l1+l2=l-1} sum_{a1+a2=a} sum_m R[l1][a1][q][m] R[l2][a2][m][s].
//
// Homogeneity: with the offset grade t = l+a and the slice polynomials
//   C_t(y;u,v) = sum_{a<t} y^a R[t-a][a][u][v]        (stored as E[t][u][v] at y=y_j)
// the whole split at output grade W is, for every point y_j,
//
//   Phi_W(y_j;q,s) = sum_{tau1=1}^{W-2} sum_m E[tau1-q][q][m] * E[W-1-tau1][m][s]
//                  = sum_a y_j^a SPLIT[W-q-a][a][q][s].
//
// GEMM form.  Fix W and j.  For each g2 = 1..W-2 put tau1 = W-1-g2 and
//   A[q][m] = C_{tau1-q}(y_j;q,m),  q = 0..tau1-1,  m = 0..tau1-1   (tau1 x tau1)
//   B[m][s] = C_{g2}(y_j;m,s),      m = 0..tau1-1,  s = 0..W-3      (tau1 x (W-2))
// (both zero-padded outside their supports).  Then Phi_W(y_j) = sum_{g2} A*B.
// A's row q has scount(tau1-q,q) = tau1-1 entries (tau1 for q = tau1-1); B is an
// upper staircase, row m holding scount(g2,m) = g2+m-1 entries (m+1 for g2 = 1).
// The staircase is exploited by NC-wide column blocks with a per-block start row
//   mstart(s0) = (g2 == 1 ? s0 : max(0, s0+2-g2)).
//
// Degree pruning.  SPLIT[l][.] vanishes for l < 3, so deg_y Phi_W(.;q,.) <= W-q-3
// and coordinate q needs exactly the W-q-2 points y = 1..W-q-2.  Equivalently the
// 1-based point y = j needs only the rows q <= W-2-j of A (0-based: q < W-2-j).
//
// Exact arithmetic without reduction inside the GEMM.  Storage is u16 for P < 2^16
// and u32 for P < 2^21; the GEMM accumulates in binary64, where every integer
// below 2^53 is exact.  Entries are < P, so one product is < (P-1)^2 and the
// accumulator stays exact for PRODLIMIT = floor(2^53/(P-1)^2) products.  The engine
// counts the products accumulated into a C entry (bounded by sum of the tau1 of the
// g2 blocks done since the last reduction) and reduces C modulo P whenever the next
// block could exceed PRODLIMIT.  For P < 2^16 PRODLIMIT >= 2^21 while the total
// number of products per output entry is at most sum_{tau1<W} tau1 < N^2/2 <= 45000,
// so a single reduction per (W,j) suffices; for P < 2^21 PRODLIMIT = 2048 and a
// reduction happens roughly every 2048/tau1 blocks.
//
// Build:   ./build.sh          (see README.md)
//   -DMODP=<prime>             modulus, must be < 2^21
//   -DSTORE_BITS=16|32         storage width (default: 16 iff MODP < 2^16)
//   -DUSE_CBLAS                use cblas_dgemm on the packed double panels
//   -DNO_NEON                  disable the hand-written NEON micro-kernel

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif
#include <sys/resource.h>
#if defined(__aarch64__) && !defined(NO_NEON)
#include <arm_neon.h>
#define GEMM_NEON 1
#endif
#ifdef USE_CBLAS
#include <cblas.h>
#endif

using u16 = std::uint16_t;
using u32 = std::uint32_t;
using u64 = std::uint64_t;

// ---------------------------------------------------------------- modulus --
#ifndef MODP
#define MODP 65521ull
#endif
static constexpr u64 P = MODP;
static_assert(P >= 3, "P too small");
static_assert(P < (1ull << 21), "the GEMM exactness argument requires P < 2^21");

#ifndef STORE_BITS
#  if MODP < 65536ull
#    define STORE_BITS 16
#  else
#    define STORE_BITS 32
#  endif
#endif
#if STORE_BITS == 16
using ST = u16;
static_assert(P < 65536ull, "u16 storage requires P < 2^16");
static const char* STORE_NAME = "u16";
#elif STORE_BITS == 32
using ST = u32;
static const char* STORE_NAME = "u32";
#else
#error "STORE_BITS must be 16 or 32"
#endif

static constexpr u64 MAXPROD  = (P - 1) * (P - 1);
static constexpr u64 PRODLIMIT = (1ull << 53) / MAXPROD;   // exact-accumulation budget
static_assert(PRODLIMIT >= 64, "prime too large for exact binary64 accumulation");

static const u64 BARR = (u64)((((__uint128_t)1) << 64) / P);
static inline u32 redP(u64 x) {                 // full reduction, any 64-bit x
    u64 q = (u64)(((__uint128_t)x * BARR) >> 64);
    u64 r = x - q * P;
    while (r >= P) r -= P;
    return (u32)r;
}
static inline u64 partial(u64 pr) {             // congruent value < 3P
    u64 q = (u64)(((__uint128_t)pr * BARR) >> 64);
    return pr - q * P;
}
static inline u32 addm(u32 a, u32 b) { u32 s = a + b; return s >= (u32)P ? s - (u32)P : s; }
static inline u32 mulm(u32 a, u32 b) { return redP((u64)a * b); }
static u32 powm(u32 b, u64 e) { u32 r = 1; while (e) { if (e & 1) r = mulm(r, b); b = mulm(b, b); e >>= 1; } return r; }

// acc[0..n) += v * B[0..n)  with partially reduced u64 accumulators
static inline void axpyST(u64* __restrict C, const ST* __restrict B, u32 v, int n) {
    for (int s = 0; s < n; ++s) C[s] += partial((u64)v * B[s]);
}

// ----------------------------------------------------------------- shapes --
static inline int slen(int a, int q) { return a == 0 ? q + 1 : a + q; }
static inline int scount(int t, int u) { return t == 1 ? u + 1 : t + u - 1; }

// ------------------------------------------------------------ micro-kernel --
static constexpr int MR = 4, NR = 8, NCB = 64;   // NCB must be a multiple of NR

// C (MR x NR block, row stride ldc) += Apan (MR rows of lda doubles) * Bp
// Bp is (m1-m0) x ldb, row (m-m0) holding the NR columns of this block.
static inline void micro_mrxnr(double* __restrict C, size_t ldc,
                               const double* __restrict Apan, size_t lda,
                               const double* __restrict Bp, size_t ldb,
                               int m0, int m1) {
#ifdef GEMM_NEON
    float64x2_t c00 = vld1q_f64(C + 0 * ldc + 0), c01 = vld1q_f64(C + 0 * ldc + 2),
                c02 = vld1q_f64(C + 0 * ldc + 4), c03 = vld1q_f64(C + 0 * ldc + 6);
    float64x2_t c10 = vld1q_f64(C + 1 * ldc + 0), c11 = vld1q_f64(C + 1 * ldc + 2),
                c12 = vld1q_f64(C + 1 * ldc + 4), c13 = vld1q_f64(C + 1 * ldc + 6);
    float64x2_t c20 = vld1q_f64(C + 2 * ldc + 0), c21 = vld1q_f64(C + 2 * ldc + 2),
                c22 = vld1q_f64(C + 2 * ldc + 4), c23 = vld1q_f64(C + 2 * ldc + 6);
    float64x2_t c30 = vld1q_f64(C + 3 * ldc + 0), c31 = vld1q_f64(C + 3 * ldc + 2),
                c32 = vld1q_f64(C + 3 * ldc + 4), c33 = vld1q_f64(C + 3 * ldc + 6);
    const double* b = Bp;
    const double* a0 = Apan + 0 * lda, *a1 = Apan + 1 * lda,
                * a2 = Apan + 2 * lda, *a3 = Apan + 3 * lda;
    for (int m = m0; m < m1; ++m, b += ldb) {
        float64x2_t b0 = vld1q_f64(b), b1 = vld1q_f64(b + 2),
                    b2 = vld1q_f64(b + 4), b3 = vld1q_f64(b + 6);
        const double v0 = a0[m], v1 = a1[m], v2 = a2[m], v3 = a3[m];
        c00 = vfmaq_n_f64(c00, b0, v0); c01 = vfmaq_n_f64(c01, b1, v0);
        c02 = vfmaq_n_f64(c02, b2, v0); c03 = vfmaq_n_f64(c03, b3, v0);
        c10 = vfmaq_n_f64(c10, b0, v1); c11 = vfmaq_n_f64(c11, b1, v1);
        c12 = vfmaq_n_f64(c12, b2, v1); c13 = vfmaq_n_f64(c13, b3, v1);
        c20 = vfmaq_n_f64(c20, b0, v2); c21 = vfmaq_n_f64(c21, b1, v2);
        c22 = vfmaq_n_f64(c22, b2, v2); c23 = vfmaq_n_f64(c23, b3, v2);
        c30 = vfmaq_n_f64(c30, b0, v3); c31 = vfmaq_n_f64(c31, b1, v3);
        c32 = vfmaq_n_f64(c32, b2, v3); c33 = vfmaq_n_f64(c33, b3, v3);
    }
    vst1q_f64(C + 0 * ldc + 0, c00); vst1q_f64(C + 0 * ldc + 2, c01);
    vst1q_f64(C + 0 * ldc + 4, c02); vst1q_f64(C + 0 * ldc + 6, c03);
    vst1q_f64(C + 1 * ldc + 0, c10); vst1q_f64(C + 1 * ldc + 2, c11);
    vst1q_f64(C + 1 * ldc + 4, c12); vst1q_f64(C + 1 * ldc + 6, c13);
    vst1q_f64(C + 2 * ldc + 0, c20); vst1q_f64(C + 2 * ldc + 2, c21);
    vst1q_f64(C + 2 * ldc + 4, c22); vst1q_f64(C + 2 * ldc + 6, c23);
    vst1q_f64(C + 3 * ldc + 0, c30); vst1q_f64(C + 3 * ldc + 2, c31);
    vst1q_f64(C + 3 * ldc + 4, c32); vst1q_f64(C + 3 * ldc + 6, c33);
#else
    double acc[MR][NR];
    for (int i = 0; i < MR; ++i)
        for (int k = 0; k < NR; ++k) acc[i][k] = C[(size_t)i * ldc + k];
    for (int m = m0; m < m1; ++m) {
        const double* b = Bp + (size_t)(m - m0) * ldb;
        for (int i = 0; i < MR; ++i) {
            const double v = Apan[(size_t)i * lda + m];
            for (int k = 0; k < NR; ++k) acc[i][k] += v * b[k];
        }
    }
    for (int i = 0; i < MR; ++i)
        for (int k = 0; k < NR; ++k) C[(size_t)i * ldc + k] = acc[i][k];
#endif
}

// exact reduction of a non-negative integral double < 2^53 modulo P
static inline void reduce_block(double* __restrict C, size_t n) {
    const double Pd = (double)P, Pinv = 1.0 / (double)P;
    for (size_t i = 0; i < n; ++i) {
        double x = C[i];
        double q = std::floor(x * Pinv);
        double r = x - q * Pd;          // exact: both operands are integers < 2^53
        r = (r < 0.0) ? r + Pd : r;
        r = (r >= Pd) ? r - Pd : r;
        C[i] = r;
    }
}

struct Counters {
    unsigned long long split_struct = 0;   // structural multiply-adds of the split
    unsigned long long split_fma = 0;      // multiply-adds actually issued by the GEMM
    unsigned long long pack_a = 0, pack_b = 0, reduce_ops = 0;
    unsigned long long interp = 0;
    unsigned long long absorb = 0;
    unsigned long long gmults = 0;
    unsigned long long band_adds = 0;
};

struct Scratch {
    std::vector<double> A, B, C;
    void ensure(size_t na, size_t nb, size_t nc) {
        if (A.size() < na) A.assign(na, 0.0);
        if (B.size() < nb) B.assign(nb, 0.0);
        if (C.size() < nc) C.assign(nc, 0.0);
    }
};

// ------------------------------------------------------------------ engine --
struct Engine {
    int N, J, JP;                 // J = N+1 nominal points, JP = points actually stored
    bool prune = false;
    bool spill = false;
    std::string spillpath;
    FILE* spillf = nullptr;

    // R: grade-major.  Grade w block holds (l,a) rows, l = 1..w, a = 0..w-l,
    // q = w-l-a, of length slen(a,q).
    std::vector<u64> gbase;       // grade -> start of the grade block in the full table
    std::vector<u64> glb;         // glb[w*(N+2)+l] -> offset of (l,a=0) inside grade w
    std::vector<u64> gsize;       // grade -> number of entries
    std::vector<ST>  R;           // full table (empty while spilling)
    std::vector<ST>  Gbuf[2];     // rolling grade buffers while spilling
    bool rfull = false;
    u64 RSIZE = 0;

    std::vector<u64> ebase;       // t -> base offset inside one evaluation point
    u64 ESIZE = 0;
    std::vector<ST>  E;           // JP * ESIZE
    std::vector<u32> ypow;        // JP x (N+1)
    std::vector<u32> Wpre;        // inverse Vandermonde of every prefix point set 1..n
    std::vector<u64> woff;
    inline const u32* wmat(int n) const { return &Wpre[woff[n]]; }

    std::vector<ST>  Cbuf;        // JP x SQ x SS evaluated split values of the grade
    int SQ = 1, SS = 1;
    std::vector<Scratch> scr;
    Counters cnt;
    bool support_violation = false;
    bool degree_violation = false;
    bool eval_violation = false;
    int nthreads = 1;
    double t_bands = 0, t_split = 0, t_interp = 0, t_absorb = 0;

    inline u64 goff(int w, int l, int a) const {
        const int k = w - l;
        return glb[(size_t)w * (N + 2) + l] + (a == 0 ? 0ull : (u64)(k + 1) + (u64)(a - 1) * k);
    }
    inline ST* gblock(int w) { return rfull ? &R[gbase[w]] : Gbuf[w & 1].data(); }
    inline const ST* gblock(int w) const { return rfull ? &R[gbase[w]] : Gbuf[w & 1].data(); }
    inline ST* rrow(int l, int a, int q) { return gblock(l + a + q) + goff(l + a + q, l, a); }
    inline const ST* rrow(int l, int a, int q) const { return gblock(l + a + q) + goff(l + a + q, l, a); }
    inline u64 eoff(int t, int u) const {
        return ebase[t] + (t == 1 ? (u64)u * (u + 1) / 2 : (u64)(t - 1) * u + (u64)u * (u - 1) / 2);
    }

    Engine(int N_, int threads, bool need_eval, bool prune_, bool spill_, const char* sp)
        : N(N_), J(N_ + 1), prune(prune_), spill(spill_), nthreads(threads) {
        JP = prune ? std::max(1, N - 2) : J;
        if (sp) spillpath = sp;
        // ---- R layout (grade-major)
        gbase.assign(N + 2, 0);
        gsize.assign(N + 2, 0);
        glb.assign((size_t)(N + 2) * (N + 2), 0);
        u64 off = 0;
        u64 gmax = 0;
        for (int w = 1; w <= N; ++w) {
            gbase[w] = off;
            u64 o = 0;
            for (int l = 1; l <= w; ++l) {
                glb[(size_t)w * (N + 2) + l] = o;
                const int k = w - l;
                o += (u64)(k + 1) + (u64)k * k;
            }
            gsize[w] = o;
            gmax = std::max(gmax, o);
            off += o;
        }
        gbase[N + 1] = off;
        RSIZE = off;
        if (spill) {
            Gbuf[0].assign(gmax, 0); Gbuf[1].assign(gmax, 0);
            rfull = false;
            spillf = fopen(spillpath.c_str(), "w+b");
            if (!spillf) { fprintf(stderr, "cannot open spill file %s\n", spillpath.c_str()); exit(2); }
        } else {
            R.assign(RSIZE, 0);
            rfull = true;
        }
        if (!need_eval) return;

        // ---- E layout
        ebase.assign(N + 2, 0);
        u64 eo = 0;
        for (int t = 1; t <= N; ++t) { ebase[t] = eo; for (int u = 0; u <= N - t; ++u) eo += scount(t, u); }
        ebase[N + 1] = eo;
        ESIZE = eo;
        E.assign((size_t)JP * ESIZE, 0);

        ypow.assign((size_t)JP * (N + 1), 0u);
        for (int j = 0; j < JP; ++j) {
            u32 y = (u32)((j + 1) % P), v = 1;
            for (int k = 0; k <= N; ++k) { ypow[(size_t)j * (N + 1) + k] = v; v = mulm(v, y); }
        }
        build_inverse_vandermonde();
        SQ = std::max(1, N - 2); SS = std::max(1, N - 2);
        Cbuf.assign((size_t)JP * SQ * SS, 0);
        scr.resize(nthreads);
    }
    ~Engine() { if (spillf) fclose(spillf); }

    static inline u32 negm(u32 a) { return a == 0 ? 0u : (u32)(P - a); }
    static void vandermonde(int n, u32* W) {
        std::vector<u32> master(n + 1, 0u); master[0] = 1;
        for (int i = 0; i < n; ++i) {
            u32 x = (u32)((i + 1) % P);
            for (int k = n; k >= 1; --k) master[k] = addm(master[k - 1], negm(mulm(x, master[k])));
            master[0] = negm(mulm(x, master[0]));
        }
        std::vector<u32> b(n, 0u);
        for (int i = 0; i < n; ++i) {
            u32 x = (u32)((i + 1) % P), carry = 0;
            for (int k = n; k >= 1; --k) { carry = addm(master[k], mulm(carry, x)); b[k - 1] = carry; }
            u32 den = 0;
            for (int k = n - 1; k >= 0; --k) den = addm(mulm(den, x), b[k]);
            u32 inv = powm(den, P - 2);
            for (int k = 0; k < n; ++k) W[(size_t)k * n + i] = mulm(b[k], inv);
        }
    }
    void build_inverse_vandermonde() {
        woff.assign(JP + 1, 0);
        u64 o = 0;
        for (int n = 1; n <= JP; ++n) { woff[n] = o; o += (u64)n * n; }
        Wpre.assign(o, 0u);
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic) num_threads(nthreads)
#endif
        for (int n = 1; n <= JP; ++n) vandermonde(n, &Wpre[woff[n]]);
    }

    // ---------------------------------------------------- bands and D term --
    void bands(int w) {
        if (!rfull) std::fill(Gbuf[w & 1].begin(), Gbuf[w & 1].begin() + gsize[w], (ST)0);
        std::vector<u32> acc(N + 3, 0u);
        for (int l = 1; l <= w; ++l) {                       // BAND1
            int c = w - 1 - l;
            if (c < 0) continue;
            std::fill(acc.begin(), acc.begin() + (c + 1), 0u);
            for (int a = 0; a <= c + 1; ++a) {
                int q = c + 1 - a;
                if (a >= 1) {
                    ST* dst = rrow(l, a, q);
                    int lim = std::min(slen(a, q), c + 1);
                    for (int i = 0; i < lim; ++i) dst[i] = (ST)addm(dst[i], acc[i]);
                }
                if (a <= c) {
                    const ST* src = rrow(l, a, c - a);
                    int Ls = slen(a, c - a);
                    cnt.band_adds += Ls;
                    for (int i = 0; i < Ls; ++i) acc[i] = addm(acc[i], src[i]);
                }
            }
        }
        for (int a = 0; a < w; ++a) {                        // BAND2
            int c2 = w - 1 - a;
            if (c2 < 1) continue;
            int L = slen(a, c2);
            std::fill(acc.begin(), acc.begin() + (L + 1), 0u);
            for (int l = c2; l >= 1; --l) {
                const ST* src = rrow(l, a, c2 - l);
                int Ls = slen(a, c2 - l);
                cnt.band_adds += Ls;
                for (int i = 0; i < Ls; ++i) acc[i] = addm(acc[i], src[i]);
                int q = c2 + 1 - l;
                ST* dst = rrow(l, a, q);
                int Ld = slen(a, q);
                for (int i = 0; i < Ld; ++i) dst[i] = (ST)addm(dst[i], acc[i]);
            }
        }
        for (int l = 1; l <= w; ++l)                         // D term
            for (int a = 0; a <= w - l; ++a) {
                int q = w - l - a;
                ST* dst = rrow(l, a, q);
                if (l == 1) { if (a == 0) dst[q] = (ST)addm(dst[q], 1u); }
                else {
                    const ST* src = rrow(l - 1, a, q);
                    int Ls = slen(a, q);
                    cnt.band_adds += Ls;
                    for (int i = 0; i < Ls; ++i) dst[i] = (ST)addm(dst[i], addm(src[i], src[i]));
                }
            }
    }

    // ------------------------------------------------------ literal split ---
    void split_naive(int w) {
        std::vector<u64> row(N + 3, 0u);
        for (int l = 1; l <= w; ++l)
            for (int a = 0; a <= w - l; ++a) {
                int q = w - l - a;
                int L = slen(a, q);
                if (l < 3) continue;
                std::fill(row.begin(), row.begin() + L, 0ull);
                bool any = false;
                for (int l1 = 1; l1 <= l - 2; ++l1) {
                    int l2 = l - 1 - l1;
                    for (int a1 = 0; a1 <= a; ++a1) {
                        int a2 = a - a1;
                        const ST* A = rrow(l1, a1, q);
                        int la = slen(a1, q);
                        for (int m = 0; m < la; ++m) {
                            int lb = std::min(slen(a2, m), L);
                            cnt.split_struct += lb;
                            u32 v = A[m];
                            if (!v) continue;
                            cnt.split_fma += lb;
                            axpyST(row.data(), rrow(l2, a2, m), v, lb);
                            any = true;
                        }
                    }
                }
                if (!any) continue;
                ST* dst = rrow(l, a, q);
                for (int s = 0; s < L; ++s) if (row[s]) dst[s] = (ST)addm(dst[s], redP(row[s]));
            }
    }

    // ---------------------------------------------------------- GEMM split --
    void split_gemm(int w) {
        if (w < 3) return;
        const int nq = w - 2, ns = w - 2;
        const int nsPad = ((ns + NR - 1) / NR) * NR;
        const int npts = prune ? std::min(JP, w - 2) : JP;
        unsigned long long ss = 0, sf = 0, pa = 0, pb = 0, rd = 0;
        double ts = now_();
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic, 1) num_threads(nthreads) \
        reduction(+ : ss, sf, pa, pb, rd)
#endif
        for (int j = 0; j < npts; ++j) {
#ifdef _OPENMP
            const int tid = omp_get_thread_num();
#else
            const int tid = 0;
#endif
            const int qcap = prune ? (w - 2 - j) : nq;
            const int Mmax = std::min(nq, qcap);
            if (Mmax <= 0) continue;
            const int MP = ((Mmax + MR - 1) / MR) * MR;
            Scratch& S = scr[tid];
#ifdef USE_CBLAS
            S.ensure((size_t)MP * (nq + 1), (size_t)(ns + 1) * nsPad, (size_t)MP * nsPad);
#else
            S.ensure((size_t)MP * (nq + 1), (size_t)(ns + 1) * NCB, (size_t)MP * nsPad);
#endif
            double* C = S.C.data();
            std::fill(C, C + (size_t)MP * nsPad, 0.0);
            const ST* Ej = &E[(size_t)j * ESIZE];
            u64 pc = 0;
            for (int tau1 = 1; tau1 <= w - 2; ++tau1) {
                const int g2 = w - 1 - tau1;
                const int M = std::min(tau1, Mmax);
                const int K = tau1;
                if (pc + (u64)K > PRODLIMIT) {
                    reduce_block(C, (size_t)MP * nsPad);
                    rd += (unsigned long long)MP * nsPad;
                    pc = 1;
                }
                pc += (u64)K;
                // structural madd count (closed form, see header)
                {
                    auto pre = [&](long long n) -> unsigned long long {
                        if (n <= 0) return 0;
                        return (g2 == 1) ? (unsigned long long)(n * (n + 1) / 2)
                                         : (unsigned long long)(n * (long long)(g2 - 1) + n * (n - 1) / 2);
                    };
                    const bool full = (M == tau1);
                    ss += (unsigned long long)(M - (full ? 1 : 0)) * pre(tau1 - 1) + (full ? pre(tau1) : 0);
                }
                const int MPb = ((M + MR - 1) / MR) * MR;
                // ---- pack A (MPb rows x K), row-major
                double* Ap = S.A.data();
                for (int i = 0; i < MPb; ++i) {
                    double* dst = Ap + (size_t)i * K;
                    if (i < M) {
                        const int t = tau1 - i;
                        const ST* src = Ej + eoff(t, i);
                        const int La = std::min(scount(t, i), K);
                        for (int m = 0; m < La; ++m) dst[m] = (double)src[m];
                        for (int m = La; m < K; ++m) dst[m] = 0.0;
                    } else {
                        for (int m = 0; m < K; ++m) dst[m] = 0.0;
                    }
                }
                pa += (unsigned long long)MPb * K;
#ifdef USE_CBLAS
                {
                    // full K x ns packed B, no staircase blocking (reference path)
                    double* Bp = S.B.data();
                    u64 eo = eoff(g2, 0);
                    for (int m = 0; m < K; ++m) {
                        const ST* src = Ej + eo;
                        const int lm = std::min(scount(g2, m), ns);
                        eo += scount(g2, m);
                        double* d = Bp + (size_t)m * nsPad;
                        for (int c = 0; c < lm; ++c) d[c] = (double)src[c];
                        for (int c = lm; c < nsPad; ++c) d[c] = 0.0;
                    }
                    pb += (unsigned long long)K * nsPad;
                    cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, MPb, nsPad, K,
                                1.0, Ap, K, Bp, nsPad, 1.0, C, nsPad);
                    sf += (unsigned long long)MPb * nsPad * K;
                }
#else
                for (int s0 = 0; s0 < ns; s0 += NCB) {
                    const int nc = std::min(NCB, ns - s0);
                    const int ncPad = ((nc + NR - 1) / NR) * NR;
                    int mstart = (g2 == 1) ? s0 : (s0 + 2 - g2);
                    if (mstart < 0) mstart = 0;
                    if (mstart >= K) continue;
                    double* Bp = S.B.data();
                    u64 eo = eoff(g2, mstart);
                    for (int m = mstart; m < K; ++m) {
                        const ST* src = Ej + eo;
                        const int lm = std::min(scount(g2, m), ns);
                        eo += scount(g2, m);
                        double* d = Bp + (size_t)(m - mstart) * ncPad;
                        int have = lm - s0;
                        if (have < 0) have = 0;
                        if (have > ncPad) have = ncPad;
                        const ST* s2 = src + s0;
                        for (int c = 0; c < have; ++c) d[c] = (double)s2[c];
                        for (int c = have; c < ncPad; ++c) d[c] = 0.0;
                    }
                    pb += (unsigned long long)(K - mstart) * ncPad;
                    for (int i0 = 0; i0 < MPb; i0 += MR)
                        for (int c0 = 0; c0 < ncPad; c0 += NR)
                            micro_mrxnr(C + (size_t)i0 * nsPad + s0 + c0, (size_t)nsPad,
                                        Ap + (size_t)i0 * K, (size_t)K,
                                        Bp + c0, (size_t)ncPad, mstart, K);
                    sf += (unsigned long long)MPb * ncPad * (K - mstart);
                }
#endif
            }
            reduce_block(C, (size_t)Mmax * nsPad);
            rd += (unsigned long long)Mmax * nsPad;
            for (int q = 0; q < Mmax; ++q) {
                ST* out = &Cbuf[((size_t)j * SQ + q) * SS];
                const double* c = C + (size_t)q * nsPad;
                for (int s = 0; s < ns; ++s) out[s] = (ST)(u32)c[s];
            }
        }
        cnt.split_struct += ss; cnt.split_fma += sf;
        cnt.pack_a += pa; cnt.pack_b += pb; cnt.reduce_ops += rd;
        t_split += now_() - ts;

        // ------------------------------------------- interpolate and absorb --
        double ti = now_();
        unsigned long long ic = 0;
        int viol = 0, dviol = 0, eviol = 0;
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic) num_threads(nthreads) \
        reduction(+ : ic) reduction(| : viol, dviol, eviol)
#endif
        for (int q = 0; q < nq; ++q) {
            const int deg1 = w - q - 2;                  // number of possibly nonzero a's
            const int np = prune ? deg1 : std::min(JP, w - q);
            const int na = np;
            const u32* Wm = wmat(np);
            std::vector<u64> acc(ns);
            // extra evaluation points kept for the consistency check (unpruned only)
            const int jx0 = np, jx1 = prune ? np : std::min(npts, np + 2);
            std::vector<u32> coef(jx1 > jx0 ? (size_t)na * ns : 0, 0u);
            for (int a = 0; a < na; ++a) {
                std::fill(acc.begin(), acc.end(), 0ull);
                const u32* wrow = Wm + (size_t)a * np;
                for (int j = 0; j < np; ++j)
                    axpyST(acc.data(), &Cbuf[((size_t)j * SQ + q) * SS], wrow[j], ns);
                ic += (unsigned long long)ns * np;
                const int l = w - q - a;
                const int L = slen(a, q);
                ST* dst = rrow(l, a, q);
                for (int s = 0; s < ns; ++s) {
                    u32 v = redP(acc[s]);
                    if (jx1 > jx0) coef[(size_t)a * ns + s] = v;
                    if (!v) continue;
                    if (a >= deg1) { dviol = 1; continue; }   // deg_y Phi <= w-q-3
                    if (s >= L) { viol = 1; continue; }
                    dst[s] = (ST)addm(dst[s], v);
                }
            }
            for (int j = jx0; j < jx1; ++j) {              // Horner check at unused points
                const u32* yp = &ypow[(size_t)j * (N + 1)];
                const ST* got = &Cbuf[((size_t)j * SQ + q) * SS];
                for (int s = 0; s < ns; ++s) {
                    u64 v = 0;
                    for (int a = 0; a < na; ++a) v += partial((u64)coef[(size_t)a * ns + s] * yp[a]);
                    if (redP(v) != (u32)got[s]) eviol = 1;
                }
            }
        }
        cnt.interp += ic;
        if (viol) support_violation = true;
        if (dviol) degree_violation = true;
        if (eviol) eval_violation = true;
        t_interp += now_() - ti;
    }

    // ------------------------------------------------- absorb grade w -> E --
    void absorb(int w) {
        double ta = now_();
        unsigned long long ac = 0;
#ifdef _OPENMP
#pragma omp parallel for schedule(static) num_threads(nthreads) reduction(+ : ac)
#endif
        for (int j = 0; j < JP; ++j) {
            ST* Ej = &E[(size_t)j * ESIZE];
            const u32* yp = &ypow[(size_t)j * (N + 1)];
            std::vector<u64> acc(N + 3);
            for (int t = 1; t <= w; ++t) {
                const int q = w - t;
                const int len = scount(t, q);
                std::fill(acc.begin(), acc.begin() + len, 0ull);
                for (int a = 0; a < t; ++a) {
                    const int l = t - a;
                    const int Ls = slen(a, q);
                    ac += Ls;
                    axpyST(acc.data(), rrow(l, a, q), yp[a], Ls);
                }
                ST* dst = Ej + eoff(t, q);
                for (int i = 0; i < len; ++i) dst[i] = (ST)redP(acc[i]);
            }
        }
        cnt.absorb += ac;
        t_absorb += now_() - ta;
    }

    static double now_() {
        using namespace std::chrono;
        return duration<double>(steady_clock::now().time_since_epoch()).count();
    }

    void run(int mode) {                       // 0 = gemm, 1 = naive
        for (int w = 1; w <= N; ++w) {
            double tb = now_();
            bands(w);
            t_bands += now_() - tb;
            if (mode == 0) { split_gemm(w); absorb(w); }
            else split_naive(w);
            if (spill) {
                if (fwrite(Gbuf[w & 1].data(), sizeof(ST), gsize[w], spillf) != gsize[w]) {
                    fprintf(stderr, "spill write failed at grade %d\n", w); exit(2);
                }
            }
        }
    }

    // release E and materialize the full R table (used before the empty-stack phase)
    void finalize_tables() {
        std::vector<ST>().swap(E);
        std::vector<u32>().swap(Wpre);
        std::vector<ST>().swap(Cbuf);
        std::vector<Scratch>().swap(scr);
        if (spill) {
            fflush(spillf);
            Gbuf[0].clear(); Gbuf[0].shrink_to_fit();
            Gbuf[1].clear(); Gbuf[1].shrink_to_fit();
            R.assign(RSIZE, 0);
            rewind(spillf);
            if (fread(R.data(), sizeof(ST), RSIZE, spillf) != RSIZE) {
                fprintf(stderr, "spill read-back failed\n"); exit(2);
            }
            rfull = true;
        }
    }

    // ------------------------------------------- empty-stack extraction -----
    std::vector<u32> terms() {
        const int n1 = N + 1;
        std::vector<u32> G((size_t)n1 * n1, 0u);
        G[0] = 1;
        unsigned long long gm = 0;
        for (int mass = 1; mass <= N; ++mass) {
            for (int p = 0; p <= mass; ++p) {
                const int q = mass - p;
                u64 val = 0;
                for (int h = 0; h < p; ++h) val += G[(size_t)h * n1 + (mass - h - 1)];
                val = redP(val);
                for (int h = 0; h < q; ++h) {
                    const int delta = q - 1 - h;
                    if (delta == 0) { val += G[(size_t)p * n1 + h]; val = redP(val); continue; }
                    for (int c = 0; c <= p; ++c) {
                        const int aa = p - c;
                        const ST* row = rrow(delta, aa, h);
                        const int Ls = slen(aa, h);
                        gm += Ls;
                        const u32* Gc = &G[(size_t)c * n1];
                        for (int s = 0; s < Ls; ++s) val += partial((u64)row[s] * Gc[s]);
                    }
                    val = redP(val);
                }
                G[(size_t)p * n1 + q] = redP(val);
            }
        }
        cnt.gmults += gm;
        std::vector<u32> out(N + 1);
        for (int n = 0; n <= N; ++n) out[n] = G[(size_t)n * n1 + 0];
        return out;
    }
};

// ------------------------------------------------------------- utilities ----
static std::vector<u32> load_truth_mod(int N, const char* path) {
    FILE* f = fopen(path, "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", path); exit(2); }
    std::vector<u32> out;
    char line[8192];
    while (fgets(line, sizeof line, f)) {
        char* s = line;
        while (*s == ' ') ++s;
        if (*s == '#' || *s == '\n' || *s == 0) continue;
        long n = strtol(s, &s, 10);
        while (*s == ' ') ++s;
        u64 v = 0;
        for (; *s >= '0' && *s <= '9'; ++s) v = (v * 10 + (u64)(*s - '0')) % P;
        if (n > N) continue;
        if ((long)out.size() != n) { fprintf(stderr, "truth file out of order\n"); exit(2); }
        out.push_back((u32)v);
    }
    fclose(f);
    return out;
}
static double now() {
    using namespace std::chrono;
    return duration<double>(steady_clock::now().time_since_epoch()).count();
}
static long peak_rss_kib() { struct rusage ru; getrusage(RUSAGE_SELF, &ru); return ru.ru_maxrss; }

// self-test of the binary64 reduction used inside the GEMM
static int selftest() {
    int bad = 0;
    u64 st = 88172645463325252ull;
    for (int it = 0; it < 200000; ++it) {
        st ^= st << 13; st ^= st >> 7; st ^= st << 17;
        u64 x = st & ((1ull << 53) - 1);
        double d = (double)x;
        reduce_block(&d, 1);
        if ((u64)d != x % P) { ++bad; if (bad < 4) fprintf(stderr, "reduce mismatch x=%llu\n", (unsigned long long)x); }
    }
    // extreme values
    for (u64 x : {(u64)0, (u64)1, (u64)(P - 1), (u64)P, (u64)(P + 1),
                  (u64)((1ull << 53) - 1), (u64)(MAXPROD * PRODLIMIT)}) {
        if (x >= (1ull << 53)) continue;
        double d = (double)x; reduce_block(&d, 1);
        if ((u64)d != x % P) ++bad;
    }
    return bad;
}

int main(int argc, char** argv) {
    int N = 40, threads = 1, mode = 0;
    bool doprune = false, dospill = false, compare = false;
    const char* truth = "code/data/av12453_terms_0_150.txt";  // relative to the repository root; override with --truth
    const char* dump = nullptr;
    const char* outp = nullptr;
    const char* sidecar = nullptr;
    const char* spillp = "r_spill.bin";
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--n" && i + 1 < argc) N = atoi(argv[++i]);
        else if (a == "--threads" && i + 1 < argc) threads = atoi(argv[++i]);
        else if (a == "--engine" && i + 1 < argc) {
            std::string e = argv[++i];
            if (e == "gemm") mode = 0;
            else if (e == "naive") mode = 1;
            else if (e == "both") { mode = 0; compare = true; }
            else { fprintf(stderr, "unknown engine %s\n", e.c_str()); return 2; }
        }
        else if (a == "--prune") doprune = true;
        else if (a == "--no-prune") doprune = false;
        else if (a == "--spill") dospill = true;
        else if (a == "--spill-file" && i + 1 < argc) spillp = argv[++i];
        else if (a == "--truth" && i + 1 < argc) truth = argv[++i];
        else if (a == "--dump-r" && i + 1 < argc) dump = argv[++i];
        else if (a == "--out" && i + 1 < argc) outp = argv[++i];
        else if (a == "--sidecar" && i + 1 < argc) sidecar = argv[++i];
        else {
            fprintf(stderr,
                "usage: av12453_gemm_split --n N [--engine gemm|naive|both] [--threads K]\n"
                "       [--prune] [--spill [--spill-file F]] [--dump-r FILE]\n"
                "       [--out RESIDUES] [--sidecar FILE] [--truth FILE]\n");
            return 2;
        }
    }
    if (threads < 1) threads = 1;
    if (dospill && (dump || compare || mode == 1)) {
        fprintf(stderr, "--spill is incompatible with --dump-r / --engine naive|both\n"); return 2;
    }

    int st = selftest();
    printf("# engine av12453_gemm_split   modulus P = %llu   storage = %s   PRODLIMIT = %llu\n",
           (unsigned long long)P, STORE_NAME, (unsigned long long)PRODLIMIT);
    printf("# N = %d   threads = %d   engine = %s   prune = %s   spill = %s   kernel = %s\n",
           N, threads, mode == 0 ? "gemm" : "naive", doprune ? "ON" : "OFF",
           dospill ? "ON" : "OFF",
#ifdef USE_CBLAS
           "cblas_dgemm"
#elif defined(GEMM_NEON)
           "neon f64 4x8"
#else
           "portable f64 4x8"
#endif
    );
    if (st) { printf("SELFTEST: FAIL  %d binary64 reductions disagree with integer mod\n", st); return 1; }
    printf("selftest: OK  binary64 reduction agrees with integer mod on 2e5 random values < 2^53\n");

    double t0 = now();
    Engine eng(N, threads, mode == 0, doprune, dospill, spillp);
    double t1 = now();
    eng.run(mode);
    double t2 = now();
    eng.finalize_tables();
    std::vector<u32> terms = eng.terms();
    double t3 = now();

    const double madds_per_s = eng.t_split > 0 ? (double)eng.cnt.split_fma / eng.t_split : 0.0;
    printf("# R entries        = %llu\n", (unsigned long long)eng.RSIZE);
    if (mode == 0)
        printf("# E entries/point  = %llu   points = %d   total = %llu\n",
               (unsigned long long)eng.ESIZE, eng.JP,
               (unsigned long long)eng.ESIZE * eng.JP);
    printf("# split madds structural = %llu\n", eng.cnt.split_struct);
    printf("# split madds issued     = %llu\n", eng.cnt.split_fma);
    printf("# pack A / pack B / reduce = %llu / %llu / %llu\n",
           eng.cnt.pack_a, eng.cnt.pack_b, eng.cnt.reduce_ops);
    printf("# interp madds           = %llu\n", eng.cnt.interp);
    printf("# absorb madds           = %llu\n", eng.cnt.absorb);
    printf("# empty-stack madds      = %llu\n", eng.cnt.gmults);
    printf("# band adds              = %llu\n", eng.cnt.band_adds);
    printf("# time bands %.3fs  split %.3fs  interp %.3fs  absorb %.3fs\n",
           eng.t_bands, eng.t_split, eng.t_interp, eng.t_absorb);
    printf("# setup %.3fs  transfer %.3fs  extract %.3fs  total %.3fs\n",
           t1 - t0, t2 - t1, t3 - t2, t3 - t0);
    printf("# GEMM madds/s (all threads) = %.4g   per thread = %.4g\n",
           madds_per_s, madds_per_s / threads);
    printf("# peak RSS %ld KiB (%.2f MiB)\n", peak_rss_kib(), peak_rss_kib() / 1024.0);

    int rc = 0;
    if (mode == 0) {
        if (eng.support_violation) {
            printf("SUPPORT-VIOLATION: interpolated a nonzero split value outside slen(a,q)\n"); rc = 1;
        } else printf("support-check: OK  (no interpolated split value outside slen(a,q))\n");
        if (eng.degree_violation) {
            printf("DEGREE-VIOLATION: interpolated a nonzero y^a coefficient with a > w-q-3\n"); rc = 1;
        } else if (!doprune)
            printf("degree-check: OK  (no interpolated y^a coefficient with a > w-q-3)\n");
        if (eng.eval_violation) {
            printf("EVAL-VIOLATION: an unused evaluation point disagrees with the interpolant\n"); rc = 1;
        } else if (!doprune)
            printf("eval-check: OK  (unused evaluation points agree with the interpolant)\n");
    }

    std::vector<u32> tr = load_truth_mod(N, truth);
    int bad = -1, nchecked = 0;
    for (int n = 0; n <= N && n < (int)tr.size(); ++n) { ++nchecked; if (terms[n] != tr[n]) { bad = n; break; } }
    if (bad >= 0) { printf("CERTIFY: FAIL at n=%d  got %u want %u\n", bad, terms[bad], tr[bad]); rc = 1; }
    else printf("CERTIFY: OK  a_n mod P matches the data file for 0 <= n <= %d\n", nchecked - 1);

    if (compare) {
        double c0 = now();
        Engine ref(N, 1, false, false, false, nullptr);
        ref.run(1);
        double c1 = now();
        unsigned long long diff = 0; u64 first = 0;
        for (u64 i = 0; i < eng.RSIZE; ++i)
            if (eng.R[i] != ref.R[i]) { if (!diff) first = i; ++diff; }
        printf("# naive reference transfer %.3fs  naive split madds structural = %llu executed = %llu\n",
               c1 - c0, ref.cnt.split_struct, ref.cnt.split_fma);
        if (diff == 0)
            printf("TABLE-MATCH: OK  all %llu R entries agree with the literal-split engine\n",
                   (unsigned long long)eng.RSIZE);
        else {
            printf("TABLE-MATCH: FAIL  %llu of %llu entries differ (first flat index %llu)\n",
                   diff, (unsigned long long)eng.RSIZE, (unsigned long long)first);
            rc = 1;
        }
    }

    if (dump) {
        FILE* f = fopen(dump, "w");
        if (!f) { fprintf(stderr, "cannot write %s\n", dump); return 2; }
        fprintf(f, "# P %llu N %d\n", (unsigned long long)P, N);
        for (int l = 1; l <= N; ++l)
            for (int a = 0; a <= N - l; ++a)
                for (int q = 0; q <= N - l - a; ++q) {
                    const ST* row = eng.rrow(l, a, q);
                    int L = slen(a, q);
                    for (int s = 0; s < L; ++s)
                        if (row[s]) fprintf(f, "%d %d %d %d %u\n", l, a, q, s, (u32)row[s]);
                }
        fclose(f);
        printf("# dumped nonzero R entries to %s\n", dump);
    }

    if (outp) {
        FILE* f = fopen(outp, "w");
        if (!f) { fprintf(stderr, "cannot write %s\n", outp); return 2; }
        fprintf(f, "# prime %llu %d\n", (unsigned long long)P, N);
        fprintf(f, "# engine av12453_gemm_split storage %s threads %d prune %d\n",
                STORE_NAME, threads, doprune ? 1 : 0);
        for (int n = 0; n <= N; ++n) fprintf(f, "%d %u\n", n, terms[n]);
        fclose(f);
        printf("# residues written to %s\n", outp);
    }
    if (sidecar) {
        FILE* f = fopen(sidecar, "w");
        if (!f) { fprintf(stderr, "cannot write %s\n", sidecar); return 2; }
        u64 cks = 1469598103934665603ull;
        for (int n = 0; n <= N; ++n) { cks ^= terms[n]; cks *= 1099511628211ull; }
        fprintf(f, "{\n");
        fprintf(f, "  \"prime\": %llu,\n", (unsigned long long)P);
        fprintf(f, "  \"storage\": \"%s\",\n", STORE_NAME);
        fprintf(f, "  \"N\": %d,\n", N);
        fprintf(f, "  \"threads\": %d,\n", threads);
        fprintf(f, "  \"prune\": %d,\n", doprune ? 1 : 0);
        fprintf(f, "  \"spill\": %d,\n", dospill ? 1 : 0);
        fprintf(f, "  \"wall_s\": %.3f,\n", t3 - t0);
        fprintf(f, "  \"transfer_s\": %.3f,\n", t2 - t1);
        fprintf(f, "  \"split_s\": %.3f,\n", eng.t_split);
        fprintf(f, "  \"interp_s\": %.3f,\n", eng.t_interp);
        fprintf(f, "  \"absorb_s\": %.3f,\n", eng.t_absorb);
        fprintf(f, "  \"bands_s\": %.3f,\n", eng.t_bands);
        fprintf(f, "  \"extract_s\": %.3f,\n", t3 - t2);
        fprintf(f, "  \"peak_rss_kib\": %ld,\n", peak_rss_kib());
        fprintf(f, "  \"split_madds_structural\": %llu,\n", eng.cnt.split_struct);
        fprintf(f, "  \"split_madds_issued\": %llu,\n", eng.cnt.split_fma);
        fprintf(f, "  \"pack_a\": %llu,\n", eng.cnt.pack_a);
        fprintf(f, "  \"pack_b\": %llu,\n", eng.cnt.pack_b);
        fprintf(f, "  \"reduce_ops\": %llu,\n", eng.cnt.reduce_ops);
        fprintf(f, "  \"interp_madds\": %llu,\n", eng.cnt.interp);
        fprintf(f, "  \"absorb_madds\": %llu,\n", eng.cnt.absorb);
        fprintf(f, "  \"empty_stack_madds\": %llu,\n", eng.cnt.gmults);
        fprintf(f, "  \"band_adds\": %llu,\n", eng.cnt.band_adds);
        fprintf(f, "  \"gemm_madds_per_s_total\": %.6g,\n", madds_per_s);
        fprintf(f, "  \"gemm_madds_per_s_per_thread\": %.6g,\n", madds_per_s / threads);
        fprintf(f, "  \"E_entries\": %llu,\n", (unsigned long long)eng.ESIZE * eng.JP);
        fprintf(f, "  \"R_entries\": %llu,\n", (unsigned long long)eng.RSIZE);
        fprintf(f, "  \"residue_fnv1a64\": \"%016llx\",\n", (unsigned long long)cks);
        fprintf(f, "  \"certify\": \"%s\",\n", bad >= 0 ? "FAIL" : "OK");
        fprintf(f, "  \"certify_upto\": %d,\n", nchecked - 1);
        fprintf(f, "  \"exit_code\": %d\n", rc);
        fprintf(f, "}\n");
        fclose(f);
        printf("# sidecar written to %s\n", sidecar);
    }
    return rc;
}
