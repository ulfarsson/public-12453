// avr_table.hpp -- AVR1/AVR2 layout/indexing for the Av(12453) double tables,
// shared by tables.cpp (writer) and any consumer (e.g. sampler.cpp).
//
// Format "AVR1" (native little-endian), unscaled:
//   int32 magic = 0x41565231
//   int32 N
//   G doubles: p = 0..N, q = 0..N-p                        (nested that order)
//   R doubles: l = 1..N, a = 0..N-l, q = 0..N-l-a, s = 0..slen(a,q)-1
//   slen(a,q) = q+1 if a == 0 else a+q
//
// Format "AVR2" (native little-endian), power-of-two scaled:
//   int32 magic = 0x41565232
//   int32 N
//   int32 scale                     (exponent per grade unit; always 2 so far)
//   G doubles, R doubles            (identical layout to AVR1)
// with the stored entries
//   R'_{l,a}(q,s) = 2^{-scale*(l+a+q)} R_{l,a}(q,s),
//   G'_{(p,q)}    = 2^{-scale*(p+q)}   G_{(p,q)}.
// Scaling by a power of two is exact, so an AVR2 table multiplied back by
// 2^{scale*grade} is bit-identical to the AVR1 table of the same N.
//
// Semantics: R(l,a,q,s) = R_{l,a}(q,s) = K_l((a,q),(0,s)); the unreduced
// kernel is K_l((p,q),(c,t)) = R(l, p-c, q, t) for 0 <= c <= p, else 0.
// G(p,q) = G_{(p,q)} = H_{(p,q)}(empty);  |Av_n(12453)| = G(n,0).
// Entries outside the stored support are zero.  R_{0,a}(q,s) = [a=0][q=s].
//
// IMPORTANT: Table::R() and Table::G() always return the value *as stored*,
// i.e. the scaled value for an AVR2 table.  Consumers must apply the grade
// factors themselves (the sampler does, see sampler_core.hpp); R_true()/
// G_true() give the unscaled value when it is representable in binary64.

#ifndef AVR_TABLE_HPP
#define AVR_TABLE_HPP

#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>

namespace avr {

static const int32_t AVR_MAGIC  = 0x41565231;   // AVR1, unscaled
static const int32_t AVR2_MAGIC = 0x41565232;   // AVR2, 2^{-scale*grade} scaled
static const int32_t AVR2_SCALE = 2;            // the scale this build writes

// header size in bytes of each format
static inline size_t hdr_bytes(int32_t magic) { return magic == AVR2_MAGIC ? 12 : 8; }

// ---------------------------------------------------------------- indexing
struct Layout {
    int N = 0;
    std::vector<size_t> pstart;   // pstart[l]  : first pair index of this l (1<=l<=N)
    std::vector<size_t> qbase;    // qbase[pair]: offset in the R block of (l,a,q=0)
    std::vector<size_t> gbase;    // gbase[p]   : offset in the G block of (p,q=0)
    size_t Rtotal = 0, Gtotal = 0, nrows = 0;

    static inline int slen(int a, int q) { return a == 0 ? q + 1 : a + q; }

    // sum_{q'=0}^{q-1} slen(a,q'): offset of row q inside the (l,a) block
    static inline size_t pref(int a, int q) {
        const size_t Q = (size_t)q;
        return a == 0 ? Q * (Q + 1) / 2 : (size_t)a * Q + Q * (Q - 1) / 2;
    }

    void build(int N_) {
        N = N_;
        pstart.assign(N + 2, 0);
        size_t np = 0;
        for (int l = 1; l <= N; ++l) { pstart[l] = np; np += (size_t)(N - l + 1); }
        pstart[N + 1] = np;
        qbase.assign(np ? np : 1, 0);
        size_t off = 0; nrows = 0;
        for (int l = 1; l <= N; ++l)
            for (int a = 0; a <= N - l; ++a) {
                qbase[pstart[l] + a] = off;
                const int Q = N - l - a;
                off += pref(a, Q + 1);
                nrows += (size_t)(Q + 1);
            }
        Rtotal = off;
        gbase.assign(N + 1, 0);
        size_t g = 0;
        for (int p = 0; p <= N; ++p) { gbase[p] = g; g += (size_t)(N - p + 1); }
        Gtotal = g;
    }

    inline bool in_range_r(int l, int a, int q) const {
        return l >= 1 && l <= N && a >= 0 && q >= 0 && l + a + q <= N;
    }
    // index of R_{l,a}(q,0) inside the R block
    inline size_t rrow(int l, int a, int q) const {
        return qbase[pstart[l] + (size_t)a] + pref(a, q);
    }
    inline size_t rindex(int l, int a, int q, int s) const { return rrow(l, a, q) + (size_t)s; }
    inline size_t gindex(int p, int q) const { return gbase[p] + (size_t)q; }
    // hdr = 8 for AVR1, 12 for AVR2
    inline size_t file_offset_g(int p, int q, size_t hdr = 8) const {
        return hdr + 8 * gindex(p, q);
    }
    inline size_t file_offset_r(int l, int a, int q, int s, size_t hdr = 8) const {
        return hdr + 8 * (Gtotal + rindex(l, a, q, s));
    }
};

// ------------------------------------------------------------------ reader
struct Table {
    Layout L;
    std::vector<double> G_;
    std::vector<double> R_;
    int32_t magic = AVR_MAGIC;
    int scale = 0;                 // 0 for AVR1; 2 for AVR2 (exponent per grade)

    int N() const { return L.N; }
    bool scaled() const { return scale != 0; }
    size_t hdr() const { return hdr_bytes(magic); }

    // returns an empty error string on success
    std::string load(const std::string &path) {
        FILE *f = fopen(path.c_str(), "rb");
        if (!f) return "cannot open " + path;
        int32_t mg = 0, n32 = 0;
        if (fread(&mg, 4, 1, f) != 1 || fread(&n32, 4, 1, f) != 1) {
            fclose(f); return path + ": truncated header";
        }
        if (mg != AVR_MAGIC && mg != AVR2_MAGIC) { fclose(f); return path + ": bad magic"; }
        if (n32 < 1) { fclose(f); return path + ": bad N"; }
        magic = mg;
        scale = 0;
        if (mg == AVR2_MAGIC) {
            int32_t sc = 0;
            if (fread(&sc, 4, 1, f) != 1) { fclose(f); return path + ": truncated AVR2 header"; }
            if (sc < 1 || sc > 8) { fclose(f); return path + ": bad scale"; }
            scale = sc;
        }
        L.build(n32);
        G_.resize(L.Gtotal);
        R_.resize(L.Rtotal);
        if (fread(G_.data(), sizeof(double), L.Gtotal, f) != L.Gtotal) {
            fclose(f); return path + ": short read (G)";
        }
        size_t done = 0;
        while (done < L.Rtotal) {
            const size_t chunk = std::min<size_t>((size_t)1 << 22, L.Rtotal - done);
            if (fread(R_.data() + done, sizeof(double), chunk, f) != chunk) {
                fclose(f); return path + ": short read (R)";
            }
            done += chunk;
        }
        char extra;
        const bool trailing = (fread(&extra, 1, 1, f) == 1);
        fclose(f);
        if (trailing) return path + ": trailing bytes after the R block";
        return std::string();
    }

    inline double G(int p, int q) const {
        if (p < 0 || q < 0 || p + q > L.N) return 0.0;
        return G_[L.gindex(p, q)];
    }
    // zero-extended outside the stored support; K_0 = identity for l == 0
    inline double R(int l, int a, int q, int s) const {
        if (l == 0) return (a == 0 && q == s) ? 1.0 : 0.0;
        if (l < 0 || a < 0 || q < 0 || s < 0) return 0.0;
        if (s >= Layout::slen(a, q)) return 0.0;
        if (l + a + q > L.N) return 0.0;
        return R_[L.rindex(l, a, q, s)];
    }
    // K_l((p,q),(c,t)) = R_{l,p-c}(q,t) for 0 <= c <= p
    inline double K(int l, int p, int q, int c, int t) const {
        if (c < 0 || c > p) return 0.0;
        return R(l, p - c, q, t);
    }
    // unscaled values; +inf if the true value overflows binary64 (AVR2 only)
    inline double R_true(int l, int a, int q, int s) const {
        const double v = R(l, a, q, s);
        if (!scale || l == 0) return v;
        return std::ldexp(v, scale * (l + a + q));
    }
    inline double G_true(int p, int q) const {
        const double v = G(p, q);
        if (!scale) return v;
        return std::ldexp(v, scale * (p + q));
    }
    // contiguous row R_{l,a}(q,.) of length slen(a,q); null if out of range
    inline const double *row(int l, int a, int q) const {
        if (!L.in_range_r(l, a, q)) return nullptr;
        return R_.data() + L.rrow(l, a, q);
    }
};

}  // namespace avr
#endif
