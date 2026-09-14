// sampler_core.hpp -- exactly-uniform (up to double-precision table error)
// random sampling from Av_n(12453) by the recursive method of SAMPLER_BRIEF.md.
//
// State (paper Section 4, eq:H).  Scanning left to right, the unread values
// sorted increasingly are
//
//     U = [ B0 (p values, below b_1) ][ B1 (q values, in (b_1,b_2)) ]
//         [ I_1 ][ I_2 ] ... [ I_s ]                (blocks, above b_2)
//
// so the whole state is the single sorted array U plus (p,q) plus the block
// sizes.  I_1 (the head) is the only readable block.  Each block carries the
// target control (c,t) at which it must be exposed; those targets are the
// "frames" of the explicit stack, frames.back() == the head I_1.
//
// Weights.  Top level (empty stack) uses G; inside a block the weights are the
// protected-tail kernel R.  Both come from an AVR1 or AVR2 table in double
// precision.  Along a complete path the product of the conditional
// probabilities is 1/G(n,0) exactly in real arithmetic, hence the sampler is
// uniform up to the relative error of the tables (~3e-13 at N=150) per
// decision.
//
// Scaled (AVR2) tables.  The stored entries are R' = 2^{-2w} R (w = l+a+q)
// and G' = 2^{-2m} G (m = p+q), so the candidates of one decision, which come
// from several different grades, must be put on a common footing before they
// are compared.  Dividing every weight of a decision by the grade factor of
// the decision's own total gives, at a block state (l,(p,q),(c,t)) of grade
// w = l + (p-c) + q,
//
//   endpoints    2^{-2} R'_{l-1,p-c}(q,t)      (each of the 1 or 2 endpoints)
//   l = 1 exposure   2^{-2w} [ (p,q) = (c,t) ]
//   early band   2^{-2} R'_{l,h-c}(q+p-1-h,t)
//   last band    2^{-2} R'_{l+q-1-r,p-c}(r,t)
//   split        4^{m-1} R'_{a,p-c'}(q,m) R'_{b,c'-c}(m,t)
//
// and at the top level, control (p,q) of mass m,
//
//   early band   2^{-2} G'_{(h,q+p-1-h)}
//   zero block   2^{-2} G'_{(p,r)}
//   last band    4^{t-1} R'_{l,p-c}(r,t) G'_{(c,t)}.
//
// The weights of one decision then sum to the stored entry G'_{(p,q)} resp.
// R'_{l,p-c}(q,t), which is what --check verifies.  The two-factor products
// are formed in the BALANCED way, 2^{m-1} on each factor: the unbalanced
// R' R' underflows to zero for large n (each factor can be as small as
// 2^{-2N}), which would silently delete those candidates.  Every scale factor
// is a power of two, hence exact, so the scaled walk visits exactly the same
// candidates in exactly the same order as the unscaled one and, with the same
// seed, produces byte-identical output.

#ifndef SAMPLER_CORE_HPP
#define SAMPLER_CORE_HPP

#include "avr_table.hpp"
#include <cmath>
#include <cstdio>
#include <cstdint>
#include <string>
#include <vector>
#include <algorithm>

namespace smp {

// ------------------------------------------------------------------- PRNG
// xoshiro256** (Blackman-Vigna), seeded through splitmix64.
struct Rng {
    uint64_t s[4];
    static inline uint64_t splitmix64(uint64_t &x) {
        uint64_t z = (x += 0x9E3779B97F4A7C15ULL);
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        return z ^ (z >> 31);
    }
    void seed(uint64_t k) {
        uint64_t x = k;
        for (int i = 0; i < 4; ++i) s[i] = splitmix64(x);
        for (int i = 0; i < 8; ++i) (void)next();       // warm-up
    }
    static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
    inline uint64_t next() {
        const uint64_t r = rotl(s[1] * 5, 7) * 9;
        const uint64_t t = s[1] << 17;
        s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3];
        s[2] ^= t;   s[3] = rotl(s[3], 45);
        return r;
    }
    inline double u01() { return (double)(next() >> 11) * 0x1.0p-53; }  // [0,1)
};

// stream for sample number idx of run `seed`: independent of --threads
inline uint64_t stream_key(uint64_t seed, uint64_t idx) {
    uint64_t x = seed * 0xD1B54A32D192ED03ULL + 0x9E3779B97F4A7C15ULL * (idx + 1);
    return Rng::splitmix64(x);
}

// -------------------------------------------------------------- the sampler
struct Frame { int size, c, t; };

// a decision: kind + up to three parameters
struct Choice { int kind, x, y, z; };
// top level : kind 0 = early band (x=h) ; kind 1 = last band (x=r, y=c, z=t)
// block     : kind 0 = early band (x=h) ; kind 1 = last band (x=r)
//             kind 2 = endpoint (x=0 min, x=1 max)
//             kind 3 = interior (x=j, y=c', z=m)

struct Sampler {
    const avr::Table &T;
    int N;
    Rng rng;
    // exact powers of two for the AVR2 grade factors, exponents -2N-4 .. N+5
    std::vector<double> pw2v;
    int pw2off = 0;
    inline double pw2(int e) const { return pw2v[(size_t)(e + pw2off)]; }
    bool check = false;              // --check : weight-sum assertions
    double checktol = 1e-9;
    // state
    std::vector<int> U;
    std::vector<Frame> frames;
    int p = 0, q = 0;
    // diagnostics
    long long decisions = 0, interior_moves = 0, rescans = 0;
    double worst_rel = 0.0;
    std::string error;

    explicit Sampler(const avr::Table &t) : T(t), N(t.N()) {
        pw2off = 2 * N + 4;
        pw2v.resize((size_t)(3 * N + 10));
        for (int e = -pw2off; e + pw2off < (int)pw2v.size(); ++e)
            pw2v[(size_t)(e + pw2off)] = std::ldexp(1.0, e);
    }

    inline const double *grow(int c) const { return T.G_.data() + T.L.gindex(c, 0); }

    // ------------------------------------------------------ top-level scan
    // Enumerates the candidates of the empty-stack decision at control (p,q)
    // in the fixed order  [early band h=0..p-1] then [last band r=q-1..0,
    // c=0..p].  With STOP it stops as soon as the running sum exceeds u and
    // leaves the winning candidate in ch; without STOP it returns the total.
    // ch always ends up holding the last candidate of positive weight, which
    // is the fallback if rounding makes the scan fall short of u.
    template <bool SCALED, bool STOP>
    double scan_top(double u, Choice &ch, bool &found) const {
        double acc = 0.0;
        for (int h = 0; h < p; ++h) {
            const double gg0 = T.G(h, q + p - 1 - h);
            const double w = SCALED ? 0.25 * gg0 : gg0;
            if (w > 0.0) {
                ch.kind = 0; ch.x = h; found = true;
                acc += w;
                if (STOP && acc > u) return acc;
            }
        }
        for (int r = q - 1; r >= 0; --r) {
            const int l = q - 1 - r;                 // size of the new block
            if (l == 0) {                            // K_0 = identity: c=p, t=r
                const double g0 = T.G(p, r);
                const double w = SCALED ? 0.25 * g0 : g0;
                if (w > 0.0) {
                    ch.kind = 1; ch.x = r; ch.y = p; ch.z = r; found = true;
                    acc += w;
                    if (STOP && acc > u) return acc;
                }
                continue;
            }
            for (int c = 0; c <= p; ++c) {
                const int A = p - c;
                const double *rr = T.row(l, A, r);
                if (!rr) continue;
                const int len = std::min(avr::Layout::slen(A, r), N - c + 1);
                const double *gg = grow(c);
                double w = 0.0; int lastt = -1;
                for (int m = 0; m < len; ++m) {
                    // balanced 4^{m-1} R' G' for AVR2; plain R G for AVR1
                    const double ww = SCALED ? (rr[m] * pw2(m - 1)) * (gg[m] * pw2(m - 1))
                                             : rr[m] * gg[m];
                    if (ww > 0.0) { w += ww; lastt = m; }
                }
                if (lastt < 0) continue;
                ch.kind = 1; ch.x = r; ch.y = c; ch.z = lastt; found = true;
                if (STOP && acc + w > u) {           // pick t inside this (r,c)
                    const double res = u - acc;
                    double a2 = 0.0;
                    for (int m = 0; m < len; ++m) {
                        const double ww = SCALED ? (rr[m] * pw2(m - 1)) * (gg[m] * pw2(m - 1))
                                                 : rr[m] * gg[m];
                        if (ww > 0.0) { a2 += ww; if (a2 > res) { ch.z = m; break; } }
                    }
                    return acc + w;
                }
                acc += w;
            }
        }
        return acc;
    }

    // ---------------------------------------------------------- block scan
    // Candidate order: [endpoint(s)] [early band h=c..p-1] [last band r=0..q-1]
    // [interior j=2..l-1, c'=c..p, m].
    template <bool SCALED, bool STOP>
    double scan_blk(double u, Choice &ch, bool &found) const {
        const Frame &F = frames.back();
        const int l = F.size, c = F.c, t = F.t;
        const int A = p - c;
        double acc = 0.0;

        // ---- endpoints: min of I_1, and max of I_1 when |I_1| >= 2.
        // weight R_{l-1,A}(q,t) each; for l == 1 this is [ (p,q) == (c,t) ].
        // Scaled: 2^{-2} R'_{l-1,A}(q,t) for l >= 2, and 2^{-2w} for l == 1
        // (the exposure weight 1 sits at grade 0, the decision at grade w).
        {
            double w;
            if (SCALED) {
                w = (l >= 2) ? 0.25 * T.R(l - 1, A, q, t)
                             : ((A == 0 && q == t) ? pw2(-2 * (1 + A + q)) : 0.0);
            } else {
                w = T.R(l - 1, A, q, t);
            }
            if (w > 0.0) {
                const int nend = (l >= 2) ? 2 : 1;
                for (int e = 0; e < nend; ++e) {
                    ch.kind = 2; ch.x = e; found = true;
                    acc += w;
                    if (STOP && acc > u) return acc;
                }
            }
        }
        // ---- early band
        for (int h = c; h < p; ++h) {
            const double r0 = T.R(l, h - c, q + p - 1 - h, t);
            const double w = SCALED ? 0.25 * r0 : r0;
            if (w > 0.0) {
                ch.kind = 0; ch.x = h; found = true;
                acc += w;
                if (STOP && acc > u) return acc;
            }
        }
        // ---- last band
        for (int r = 0; r < q; ++r) {
            const double r0 = T.R(l + q - 1 - r, A, r, t);
            const double w = SCALED ? 0.25 * r0 : r0;
            if (w > 0.0) {
                ch.kind = 1; ch.x = r; found = true;
                acc += w;
                if (STOP && acc > u) return acc;
            }
        }
        // ---- interior splits
        const double *Rbase = T.R_.data();
        for (int j = 2; j <= l - 1; ++j) {
            const int a = j - 1, b = l - j;
            for (int cp = c; cp <= p; ++cp) {
                const int A1 = p - cp, A2 = cp - c;
                const double *R1 = T.row(a, A1, q);
                if (!R1) continue;
                const int len1 = avr::Layout::slen(A1, q);
                int mlo = (A2 == 0) ? t : std::max(0, t - A2 + 1);
                const int mhi = std::min(len1 - 1, N - b - A2);
                if (mlo > mhi) continue;
                size_t off = T.L.rrow(b, A2, mlo) + (size_t)t;
                double w = 0.0; int lastm = -1;
                for (int m = mlo; m <= mhi; ++m) {
                    // balanced 4^{m-1} R' R' for AVR2; plain R R for AVR1
                    const double ww = SCALED
                        ? (R1[m] * pw2(m - 1)) * (Rbase[off] * pw2(m - 1))
                        : R1[m] * Rbase[off];
                    if (ww > 0.0) { w += ww; lastm = m; }
                    off += (A2 == 0) ? (size_t)(m + 1) : (size_t)(A2 + m);
                }
                if (lastm < 0) continue;
                ch.kind = 3; ch.x = j; ch.y = cp; ch.z = lastm; found = true;
                if (STOP && acc + w > u) {           // pick m inside this (j,c')
                    const double res = u - acc;
                    double a2 = 0.0;
                    size_t o2 = T.L.rrow(b, A2, mlo) + (size_t)t;
                    for (int m = mlo; m <= mhi; ++m) {
                        const double ww = SCALED
                            ? (R1[m] * pw2(m - 1)) * (Rbase[o2] * pw2(m - 1))
                            : R1[m] * Rbase[o2];
                        if (ww > 0.0) { a2 += ww; if (a2 > res) { ch.z = m; break; } }
                        o2 += (A2 == 0) ? (size_t)(m + 1) : (size_t)(A2 + m);
                    }
                    return acc + w;
                }
                acc += w;
            }
        }
        return acc;
    }

    // -------------------------------------------------------------- moves
    inline void take(int idx, std::vector<int> &out) {
        out.push_back(U[idx]);
        U.erase(U.begin() + idx);
    }

    void apply_top(const Choice &ch, std::vector<int> &out) {
        if (ch.kind == 0) {                          // early band, letter B0[h]
            const int h = ch.x, nq = q + p - 1 - h;
            take(h, out);
            p = h; q = nq;
        } else {                                     // last band, letter B1[r]
            const int r = ch.x, l = q - 1 - r;
            take(p + r, out);
            q = r;
            if (l > 0) frames.push_back(Frame{l, ch.y, ch.z});
        }
    }

    void apply_blk(const Choice &ch, std::vector<int> &out) {
        Frame &F = frames.back();
        switch (ch.kind) {
        case 2: {                                    // endpoint of I_1
            const int base = p + q;
            take(ch.x ? base + F.size - 1 : base, out);
            if (--F.size == 0) frames.pop_back();
            break;
        }
        case 0: {                                    // early band
            const int h = ch.x, nq = q + p - 1 - h;
            take(h, out);
            p = h; q = nq;
            break;
        }
        case 1: {                                    // last band, block grows
            const int r = ch.x, add = q - 1 - r;
            take(p + r, out);
            q = r;
            F.size += add;
            break;
        }
        default: {                                   // interior split
            const int j = ch.x, l = F.size;
            const int a = j - 1, b = l - j;
            const int cc = F.c, tt = F.t;
            take(p + q + j - 1, out);
            frames.pop_back();
            frames.push_back(Frame{b, cc, tt});      // upper part, deferred
            frames.push_back(Frame{a, ch.y, ch.z});  // lower part, new head
            ++interior_moves;
            break;
        }
        }
    }

    // --------------------------------------------------------- one sample
    // Returns true on success; on failure `error` explains.
    bool sample(int n, std::vector<int> &out) {
        return T.scaled() ? sample_impl<true>(n, out) : sample_impl<false>(n, out);
    }

    template <bool SCALED>
    bool sample_impl(int n, std::vector<int> &out) {
        out.clear();
        U.resize((size_t)n);
        for (int i = 0; i < n; ++i) U[i] = i + 1;
        frames.clear();
        p = n; q = 0;
        char buf[256];

        while (true) {
            const bool top = frames.empty();
            if (top && p == 0 && q == 0) break;
            const double total = top ? T.G(p, q)
                                     : T.R(frames.back().size, p - frames.back().c,
                                           q, frames.back().t);
            if (!(total > 0.0)) {
                snprintf(buf, sizeof buf,
                         "dead state: %s total=%.17g p=%d q=%d frames=%zu",
                         top ? "top" : "blk", total, p, q, frames.size());
                error = buf; return false;
            }
            if (check) {
                Choice d{}; bool f = false;
                const double s = top ? scan_top<SCALED, false>(0.0, d, f)
                                     : scan_blk<SCALED, false>(0.0, d, f);
                const double rel = std::fabs(s - total) / total;
                if (rel > worst_rel) worst_rel = rel;
                if (!(rel <= checktol)) {
                    snprintf(buf, sizeof buf,
                             "weight-sum mismatch (%s): sum=%.17g stored=%.17g rel=%.3g"
                             " at p=%d q=%d depth=%zu",
                             top ? "top" : "blk", s, total, rel, p, q, frames.size());
                    error = buf; return false;
                }
            }
            // Draw u uniformly in [0,total) and walk the candidates.  In
            // floating point the scanned candidate weights sum to `total` only
            // up to ~1e-13 relative; if the walk runs out of mass (which needs
            // u in that last ~1e-13 sliver) we rescale u by the mass actually
            // scanned and walk again.  The result is *exactly* proportional to
            // the evaluated double weights, with no guard band and no bias.
            const double u = rng.u01() * total;
            Choice ch{}; bool found = false;
            double acc = top ? scan_top<SCALED, true>(u, ch, found)
                             : scan_blk<SCALED, true>(u, ch, found);
            if (found && acc <= u) {
                ++rescans;
                const double u2 = u * (acc / total);
                bool f2 = false;
                if (top) scan_top<SCALED, true>(u2, ch, f2); else scan_blk<SCALED, true>(u2, ch, f2);
                // if even that falls short, ch still holds the last candidate
                // of positive weight, which is a legal move
            }
            if (!found) { error = "no candidate move"; return false; }
            ++decisions;
            if (top) apply_top(ch, out); else apply_blk(ch, out);
            if ((int)out.size() > n) { error = "overrun"; return false; }
        }
        if ((int)out.size() != n || !U.empty() || p || q || !frames.empty()) {
            snprintf(buf, sizeof buf, "incomplete: len=%zu U=%zu p=%d q=%d frames=%zu",
                     out.size(), U.size(), p, q, frames.size());
            error = buf; return false;
        }
        return true;
    }
};

}  // namespace smp
#endif
