// sampler.cpp -- uniform random permutations from Av_n(12453).
//
//   sampler --table FILE --n N --count M [--seed S] [--threads T]
//           [--out FILE] [--binary FILE] [--check] [--no-avoid] [--quiet]
//
// Writes one permutation per line, values 1..n, space separated, in sample
// order (independent of --threads: sample i always uses PRNG stream
// splitmix64(seed, i)).  Every sample is verified by the independent
// trigger-lemma avoidance test in avoid12453.hpp unless --no-avoid is given.
//
// --binary FILE writes the same samples, in the same order, as a flat stream
// of little-endian uint16 values, n per record, with NO header and no
// separators; values are 1..n.  In numpy:
//
//     a = np.fromfile(FILE, dtype='<u2').reshape(-1, n)
//
// and perms_io.py reads it without numpy.  --out and --binary may be given
// together; if only --binary is given, no text is written (with neither, the
// text goes to stdout).
//
// The table may be AVR1 (unscaled) or AVR2 (power-of-two scaled); the sampler
// applies the grade factors of the scaled weights itself, and produces
// byte-identical output from the two tables of one N at the same seed.

#include "sampler_core.hpp"
#include "avoid12453.hpp"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <chrono>
#ifdef _OPENMP
#include <omp.h>
#endif

static void usage() {
    std::fprintf(stderr,
      "usage: sampler --table FILE --n N --count M [--seed S] [--threads T]\n"
      "               [--out FILE] [--binary FILE] [--check] [--checktol X]\n"
      "               [--no-avoid] [--quiet] [--stats]\n"
      "  --out FILE     text: one permutation per line, values 1..n, space separated\n"
      "  --binary FILE  little-endian uint16, n values per record, no header\n");
}

int main(int argc, char **argv) {
    std::string table, out, binout;
    int n = -1, threads = 1;
    long long count = 1;
    unsigned long long seed = 1;
    bool check = false, avoid = true, quiet = false, stats = false;
    double checktol = 1e-9;

    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        auto need = [&](const char *w) -> const char * {
            if (i + 1 >= argc) { std::fprintf(stderr, "missing value for %s\n", w); std::exit(2); }
            return argv[++i];
        };
        if      (a == "--table")   table = need("--table");
        else if (a == "--n")       n = std::atoi(need("--n"));
        else if (a == "--count")   count = std::atoll(need("--count"));
        else if (a == "--seed")    seed = std::strtoull(need("--seed"), nullptr, 10);
        else if (a == "--threads") threads = std::atoi(need("--threads"));
        else if (a == "--out")     out = need("--out");
        else if (a == "--binary")  binout = need("--binary");
        else if (a == "--check")   check = true;
        else if (a == "--checktol") { checktol = std::atof(need("--checktol")); check = true; }
        else if (a == "--no-avoid") avoid = false;
        else if (a == "--quiet")   quiet = true;
        else if (a == "--stats")   stats = true;
        else if (a == "-h" || a == "--help") { usage(); return 0; }
        else { std::fprintf(stderr, "unknown option %s\n", a.c_str()); usage(); return 2; }
    }
    if (table.empty() || n < 1 || count < 0) { usage(); return 2; }
    if (threads < 1) threads = 1;

    avr::Table T;
    const auto t_load0 = std::chrono::steady_clock::now();
    const std::string err = T.load(table);
    if (!err.empty()) { std::fprintf(stderr, "error: %s\n", err.c_str()); return 1; }
    const double t_load = std::chrono::duration<double>(std::chrono::steady_clock::now() - t_load0).count();
    if (n > T.N()) {
        std::fprintf(stderr, "error: --n %d exceeds table N = %d\n", n, T.N());
        return 1;
    }
#ifdef _OPENMP
    omp_set_num_threads(threads);
#else
    if (threads > 1) std::fprintf(stderr, "warning: built without OpenMP; 1 thread\n");
#endif

    FILE *fo = nullptr;                       // text output
    FILE *fb = nullptr;                       // binary output
    if (!out.empty()) {
        fo = std::fopen(out.c_str(), "wb");
        if (!fo) { std::fprintf(stderr, "error: cannot write %s\n", out.c_str()); return 1; }
    } else if (binout.empty()) {
        fo = stdout;                          // default: text on stdout
    }
    if (!binout.empty()) {
        fb = std::fopen(binout.c_str(), "wb");
        if (!fb) { std::fprintf(stderr, "error: cannot write %s\n", binout.c_str()); return 1; }
        if (n > 65535) { std::fprintf(stderr, "error: --binary needs n <= 65535\n"); return 1; }
    }

    // sample in blocks so that output stays in sample order with bounded memory
    const long long BLOCK = 4096;
    const size_t NB = (size_t)std::min<long long>(BLOCK, count ? count : 1);
    std::vector<std::string> lines(fo ? NB : 0);
    std::vector<unsigned char> bin(fb ? NB * (size_t)n * 2 : 0);
    std::vector<char> ok(NB, 0);
    long long bad_avoid = 0, failed = 0;
    long long tot_decisions = 0, tot_interior = 0, tot_rescans = 0;
    double worst_rel = 0.0;
    std::string firsterr;

    const auto t0 = std::chrono::steady_clock::now();
    for (long long base = 0; base < count; base += BLOCK) {
        const long long m = std::min(BLOCK, count - base);
#pragma omp parallel
        {
            smp::Sampler S(T);
            S.check = check;
            S.checktol = checktol;
            av::Scratch sc;
            std::vector<int> perm;
            char nbuf[16];
            long long dec = 0, ints = 0, res = 0, bad = 0, fail = 0;
            double wr = 0.0;
            std::string myerr;
#pragma omp for schedule(static)
            for (long long k = 0; k < m; ++k) {
                S.rng.seed(smp::stream_key(seed, (unsigned long long)(base + k)));
                ok[(size_t)k] = 0;
                if (!S.sample(n, perm)) {
                    ++fail;
                    if (myerr.empty()) myerr = "sample " + std::to_string(base + k) + ": " + S.error;
                    if (fo) lines[(size_t)k].clear();
                    continue;
                }
                ok[(size_t)k] = 1;
                if (avoid && !av::avoids_12453(perm.data(), n, sc)) {
                    ++bad;
                    if (myerr.empty()) myerr = "sample " + std::to_string(base + k) + ": contains 12453";
                }
                if (fo) {
                    std::string &s = lines[(size_t)k];
                    s.clear(); s.reserve((size_t)n * 4);
                    for (int i = 0; i < n; ++i) {
                        const int len = std::snprintf(nbuf, sizeof nbuf, "%d", perm[i]);
                        if (i) s.push_back(' ');
                        s.append(nbuf, (size_t)len);
                    }
                    s.push_back('\n');
                }
                if (fb) {                       // little-endian uint16, n per record
                    unsigned char *b = bin.data() + (size_t)k * (size_t)n * 2;
                    for (int i = 0; i < n; ++i) {
                        const unsigned v = (unsigned)perm[i];
                        b[2 * i]     = (unsigned char)(v & 0xFFu);
                        b[2 * i + 1] = (unsigned char)((v >> 8) & 0xFFu);
                    }
                }
            }
            dec = S.decisions; ints = S.interior_moves; res = S.rescans; wr = S.worst_rel;
#pragma omp critical
            {
                tot_decisions += dec; tot_interior += ints; tot_rescans += res;
                bad_avoid += bad; failed += fail;
                if (wr > worst_rel) worst_rel = wr;
                if (firsterr.empty()) firsterr = myerr;
            }
        }
        for (long long k = 0; k < m; ++k) {
            if (!ok[(size_t)k]) continue;
            if (fo) std::fwrite(lines[(size_t)k].data(), 1, lines[(size_t)k].size(), fo);
            if (fb) std::fwrite(bin.data() + (size_t)k * (size_t)n * 2, 1,
                                (size_t)n * 2, fb);
        }
    }
    const double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    if (fo && fo != stdout) std::fclose(fo);
    if (fb) std::fclose(fb);

    if (!quiet) {
        std::fprintf(stderr, "table %s (N=%d, %s%s) loaded in %.3f s\n", table.c_str(), T.N(),
                     T.scaled() ? "AVR2 scaled, scale=" : "AVR1 unscaled",
                     T.scaled() ? std::to_string(T.scale).c_str() : "", t_load);
        std::fprintf(stderr, "n=%d count=%lld threads=%d seed=%llu  %.3f s  %.1f samples/s\n",
                     n, count, threads, seed, dt, count / (dt > 0 ? dt : 1e-9));
        if (avoid) std::fprintf(stderr, "avoidance check: %s (%lld violations)\n",
                                bad_avoid ? "FAIL" : "PASS", bad_avoid);
        if (check) std::fprintf(stderr, "weight-sum check: %s (worst relative deviation %.3e, tol %.1e)\n",
                                (failed || worst_rel > checktol) ? "FAIL" : "PASS", worst_rel, checktol);
        if (stats) std::fprintf(stderr,
                                "decisions=%lld (%.2f/sample) interior=%lld (%.3f/sample) rounding-rescans=%lld\n",
                                tot_decisions, (double)tot_decisions / (count ? count : 1),
                                tot_interior, (double)tot_interior / (count ? count : 1), tot_rescans);
    }
    if (failed || bad_avoid) {
        std::fprintf(stderr, "ERROR: %lld failed samples, %lld avoidance violations; first: %s\n",
                     failed, bad_avoid, firsterr.c_str());
        return 1;
    }
    return 0;
}
