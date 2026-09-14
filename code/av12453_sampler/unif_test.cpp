// unif_test.cpp -- exact-uniformity test of the sampler at small n.
//
//   unif_test --table FILE --n N --count M [--seed S] [--threads T]
//
// 1. enumerates all n! permutations and classifies them with the naive
//    O(n^5) containment search brute_contains_12453();
// 2. cross-checks the fast trigger-lemma test contains_12453() on ALL n!
//    permutations (both avoiders and non-avoiders);
// 3. draws M samples, verifies each avoids 12453, and bins them by rank;
// 4. chi-square goodness of fit against the uniform distribution on the
//    avoiders: statistic, dof = (#avoiders - 1), and upper-tail p-value from
//    a self-contained regularized incomplete gamma Q(a,x) (plus the
//    Wilson-Hilferty normal approximation as an independent cross-check).

#include "sampler_core.hpp"
#include "avoid12453.hpp"
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>
#ifdef _OPENMP
#include <omp.h>
#endif

// ------------------------------------------------- regularized gamma Q(a,x)
static double lgammaf_(double x) { return std::lgamma(x); }

static double gser(double a, double x) {          // lower P(a,x), series
    double ap = a, sum = 1.0 / a, del = sum;
    for (int i = 1; i < 100000; ++i) {
        ap += 1.0; del *= x / ap; sum += del;
        if (std::fabs(del) < std::fabs(sum) * 1e-16) break;
    }
    return sum * std::exp(-x + a * std::log(x) - lgammaf_(a));
}
static double gcf(double a, double x) {           // upper Q(a,x), Lentz CF
    const double tiny = 1e-300;
    double b = x + 1.0 - a, c = 1.0 / tiny, d = 1.0 / b, h = d;
    for (int i = 1; i < 100000; ++i) {
        const double an = -1.0 * i * (i - a);
        b += 2.0;
        d = an * d + b; if (std::fabs(d) < tiny) d = tiny;
        c = b + an / c;  if (std::fabs(c) < tiny) c = tiny;
        d = 1.0 / d;
        const double del = d * c;
        h *= del;
        if (std::fabs(del - 1.0) < 1e-16) break;
    }
    return std::exp(-x + a * std::log(x) - lgammaf_(a)) * h;
}
// upper tail P[chi2_dof > X]
static double chi2_sf(double X, double dof) {
    const double a = 0.5 * dof, x = 0.5 * X;
    if (x <= 0) return 1.0;
    return (x < a + 1.0) ? 1.0 - gser(a, x) : gcf(a, x);
}
// Wilson-Hilferty: z ~ N(0,1)
static double wh_z(double X, double dof) {
    const double t = std::cbrt(X / dof), m = 1.0 - 2.0 / (9.0 * dof);
    return (t - m) / std::sqrt(2.0 / (9.0 * dof));
}
static double normal_sf(double z) { return 0.5 * std::erfc(z / std::sqrt(2.0)); }

// ------------------------------------------------------------- Lehmer rank
static long long lehmer_rank(const int *pi, int n, const long long *fact) {
    long long r = 0;
    for (int i = 0; i < n; ++i) {
        int c = 0;
        for (int j = i + 1; j < n; ++j) if (pi[j] < pi[i]) ++c;
        r += (long long)c * fact[n - 1 - i];
    }
    return r;
}

int main(int argc, char **argv) {
    std::string table;
    int n = 7, threads = 1;
    long long count = -1;
    unsigned long long seed = 1;
    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        auto need = [&]() -> const char * { return argv[++i]; };
        if      (a == "--table")   table = need();
        else if (a == "--n")       n = std::atoi(need());
        else if (a == "--count")   count = std::atoll(need());
        else if (a == "--seed")    seed = std::strtoull(need(), nullptr, 10);
        else if (a == "--threads") threads = std::atoi(need());
        else { std::fprintf(stderr, "unknown option %s\n", a.c_str()); return 2; }
    }
    if (table.empty() || n < 1 || n > 10) {
        std::fprintf(stderr, "usage: unif_test --table FILE --n N --count M [--seed S] [--threads T]\n");
        return 2;
    }
    avr::Table T;
    const std::string err = T.load(table);
    if (!err.empty()) { std::fprintf(stderr, "error: %s\n", err.c_str()); return 1; }
#ifdef _OPENMP
    omp_set_num_threads(threads < 1 ? 1 : threads);
#endif
    long long fact[16]; fact[0] = 1;
    for (int i = 1; i < 16; ++i) fact[i] = fact[i - 1] * i;
    const long long NF = fact[n];

    // ---- 1 & 2: enumerate, classify, cross-check the two avoidance tests
    std::vector<int> idx((size_t)NF, -1);          // rank -> avoider index
    std::vector<long long> ranks;
    std::vector<int> perm(n);
    for (int i = 0; i < n; ++i) perm[i] = i + 1;
    av::Scratch sc;
    long long disagree = 0, navoid = 0, r = 0;
    do {
        const bool cb = av::brute_contains_12453(perm.data(), n);
        const bool ct = av::contains_12453(perm.data(), n, sc);
        if (cb != ct) ++disagree;
        if (!cb) { idx[(size_t)r] = (int)navoid; ranks.push_back(r); ++navoid; }
        ++r;
    } while (std::next_permutation(perm.begin(), perm.end()));
    std::printf("n = %d :  %lld permutations, %lld avoid 12453; "
                "trigger-lemma vs brute force disagreements: %lld\n", n, NF, navoid, disagree);
    if (disagree) { std::printf("FAIL: the two avoidance tests disagree\n"); return 1; }
    if (count < 0) count = navoid * 200;

    // ---- 3: draw the samples
    std::vector<long long> obs((size_t)navoid, 0);
    long long bad = 0, fails = 0;
    const auto t0 = std::chrono::steady_clock::now();
#pragma omp parallel
    {
        smp::Sampler S(T);
        av::Scratch sc2;
        std::vector<int> pp;
        std::vector<long long> loc((size_t)navoid, 0);
        long long b = 0, f = 0;
#pragma omp for schedule(static)
        for (long long k = 0; k < count; ++k) {
            S.rng.seed(smp::stream_key(seed, (unsigned long long)k));
            if (!S.sample(n, pp)) { ++f; continue; }
            if (!av::avoids_12453(pp.data(), n, sc2)) { ++b; continue; }
            const long long rr = lehmer_rank(pp.data(), n, fact);
            const int ii = idx[(size_t)rr];
            if (ii < 0) { ++b; continue; }
            ++loc[(size_t)ii];
        }
#pragma omp critical
        {
            for (long long i = 0; i < navoid; ++i) obs[(size_t)i] += loc[(size_t)i];
            bad += b; fails += f;
        }
    }
    const double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::printf("drew %lld samples in %.2f s (%.0f/s); avoidance violations %lld, sampler failures %lld\n",
                count, dt, count / dt, bad, fails);
    if (bad || fails) { std::printf("FAIL: bad samples\n"); return 1; }

    // ---- 4: chi-square
    const double e = (double)count / (double)navoid;
    double X = 0.0;
    long long zero = 0, mn = count, mx = 0;
    for (long long i = 0; i < navoid; ++i) {
        const long long o = obs[(size_t)i];
        if (o == 0) ++zero;
        mn = std::min(mn, o); mx = std::max(mx, o);
        const double d = o - e;
        X += d * d / e;
    }
    const double dof = (double)navoid - 1.0;
    const double p = chi2_sf(X, dof);
    const double z = wh_z(X, dof);
    std::printf("every avoider seen: %s (%lld classes never sampled); counts min %lld max %lld, expected %.2f\n",
                zero ? "NO" : "YES", zero, mn, mx, e);
    std::printf("chi-square = %.4f   dof = %.0f   X2/dof = %.6f\n", X, dof, X / dof);
    std::printf("p-value (upper tail, incomplete gamma) = %.6f\n", p);
    std::printf("Wilson-Hilferty z = %+.4f   p = %.6f   (cross-check)\n", z, normal_sf(z));
    const bool ok = !zero && p > 0.001 && p < 0.999;
    std::printf("VERDICT n=%d: %s\n", n, ok ? "PASS" : "SUSPECT");
    return ok ? 0 : 1;
}
