// Independent scalar-modulus computation of Av(12453) residues.
//
// This program evaluates the protected-tail transfer recurrence for one
// requested prime.  It uses 61-bit Montgomery arithmetic and parallelizes
// the mutually independent rows of each weight layer with OpenMP.  In
// particular, it does not share the multi-prime/RNS implementation used for
// the production exact computation.
//
// Compile:
//   g++ -O3 -DNDEBUG -march=native -std=c++20 -fopenmp av12453_scalar_residue_parallel.cpp -o av12453_scalar_residue_parallel
// Run:
//   ./av12453_scalar_residue_parallel 150 --threads 8 --output av12453_residue_150.txt
//   ./av12453_scalar_residue_parallel 150 --prime 2305843009213692671 --threads 8 --output av12453_residue_150_second_prime.txt

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

#include <omp.h>

namespace {

constexpr std::uint64_t default_prime = (1ULL << 61) - 1;

std::uint64_t pow_mod(std::uint64_t a, std::uint64_t e,
                      std::uint64_t modulus) {
    std::uint64_t result = 1;
    while (e != 0) {
        if (e & 1)
            result = static_cast<std::uint64_t>(
                static_cast<unsigned __int128>(result) * a % modulus);
        a = static_cast<std::uint64_t>(
            static_cast<unsigned __int128>(a) * a % modulus);
        e >>= 1;
    }
    return result;
}

bool is_prime(std::uint64_t n) {
    if (n < 2) return false;
    for (const std::uint32_t p :
         {2U, 3U, 5U, 7U, 11U, 13U, 17U, 19U, 23U, 29U, 31U, 37U}) {
        if (n % p == 0) return n == p;
    }
    int s = 0;
    std::uint64_t d = n - 1;
    while ((d & 1) == 0) {
        ++s;
        d >>= 1;
    }
    for (const std::uint64_t a :
         {2ULL, 325ULL, 9375ULL, 28178ULL, 450775ULL, 9780504ULL,
          1795265022ULL}) {
        if (a % n == 0) continue;
        std::uint64_t x = pow_mod(a % n, d, n);
        if (x == 1 || x == n - 1) continue;
        bool witness = true;
        for (int r = 1; r < s; ++r) {
            x = static_cast<std::uint64_t>(
                static_cast<unsigned __int128>(x) * x % n);
            if (x == n - 1) {
                witness = false;
                break;
            }
        }
        if (witness) return false;
    }
    return true;
}

struct Montgomery {
    std::uint64_t modulus;
    std::uint64_t neg_inverse;
    std::uint64_t r2;
    std::uint64_t one;

    explicit Montgomery(std::uint64_t p) : modulus(p) {
        if ((p & 1) == 0 || p >= (1ULL << 62))
            throw std::invalid_argument(
                "the modulus must be an odd prime smaller than 2^62");
        std::uint64_t inverse = 1;
        for (int i = 0; i < 6; ++i) inverse *= 2 - p * inverse;
        neg_inverse = 0 - inverse;
        const std::uint64_t r = static_cast<std::uint64_t>(
            (static_cast<unsigned __int128>(1) << 64) % p);
        r2 = static_cast<std::uint64_t>(
            static_cast<unsigned __int128>(r) * r % p);
        one = to_montgomery(1);
    }

    inline std::uint64_t multiply(std::uint64_t a,
                                  std::uint64_t b) const {
        const unsigned __int128 product =
            static_cast<unsigned __int128>(a) * b;
        const std::uint64_t m = static_cast<std::uint64_t>(product)
                              * neg_inverse;
        const unsigned __int128 correction =
            static_cast<unsigned __int128>(m) * modulus;
        const std::uint64_t low = static_cast<std::uint64_t>(product);
        const std::uint64_t corrected_low =
            low + static_cast<std::uint64_t>(correction);
        const std::uint64_t carry = corrected_low < low;
        std::uint64_t result = static_cast<std::uint64_t>(product >> 64)
                             + static_cast<std::uint64_t>(correction >> 64)
                             + carry;
        if (result >= modulus) result -= modulus;
        return result;
    }

    inline std::uint64_t add(std::uint64_t a, std::uint64_t b) const {
        const std::uint64_t sum = a + b;
        return sum >= modulus ? sum - modulus : sum;
    }

    inline std::uint64_t twice(std::uint64_t a) const {
        return add(a, a);
    }

    std::uint64_t to_montgomery(std::uint64_t value) const {
        return multiply(value % modulus, r2);
    }

    std::uint64_t from_montgomery(std::uint64_t value) const {
        return multiply(value, 1);
    }
};

// Only offsets are stored.  The row length is exactly max(1,a), so retaining
// it in every RowInfo would double this random-access table through padding.
class Layout {
  public:
    explicit Layout(int n)
        : n_(n), side_(static_cast<std::size_t>(n) + 1),
          offsets_(cube_size(), 0) {
        std::uint64_t offset = 0;
        for (int weight = 1; weight <= n_; ++weight) {
            for (int ell = 1; ell <= weight; ++ell) {
                const int remainder = weight - ell;
                for (int a = 0; a <= remainder; ++a) {
                    const int q = remainder - a;
                    offsets_[index(ell, a, q)] = offset;
                    offset += static_cast<std::uint64_t>(std::max(1, a));
                }
            }
        }
        entries_ = offset;
    }

    int n() const { return n_; }
    std::uint64_t entries() const { return entries_; }

    inline std::uint64_t offset(int ell, int a, int q) const {
        return offsets_[index(ell, a, q)];
    }

  private:
    int n_;
    std::size_t side_;
    std::vector<std::uint64_t> offsets_;
    std::uint64_t entries_ = 0;

    std::size_t cube_size() const {
        if (side_ != 0 &&
            side_ > std::numeric_limits<std::size_t>::max() / side_ / side_)
            throw std::overflow_error("layout is too large");
        return side_ * side_ * side_;
    }

    inline std::size_t index(int ell, int a, int q) const {
        return (static_cast<std::size_t>(ell) * side_ + a) * side_ + q;
    }
};

struct TargetJobs {
    std::vector<std::uint16_t> ell;
    std::vector<std::uint16_t> a;
    std::vector<std::uint64_t> weight_begin;

    explicit TargetJobs(int n) : weight_begin(n + 2, 0) {
        const std::uint64_t rows =
            static_cast<std::uint64_t>(n) * (n + 1) * (n + 2) / 6;
        ell.reserve(rows);
        a.reserve(rows);
        for (int weight = 1; weight <= n; ++weight) {
            weight_begin[weight] = ell.size();
            for (int current_ell = 1; current_ell <= weight; ++current_ell) {
                for (int current_a = 0;
                     current_a <= weight - current_ell; ++current_a) {
                    ell.push_back(static_cast<std::uint16_t>(current_ell));
                    a.push_back(static_cast<std::uint16_t>(current_a));
                }
            }
        }
        weight_begin[n + 1] = ell.size();
    }
};

std::uint64_t choose(int n, int k) {
    if (n < k || k < 0) return 0;
    unsigned __int128 value = 1;
    for (int i = 1; i <= k; ++i)
        value = value * static_cast<unsigned>(n - k + i) /
                static_cast<unsigned>(i);
    if (value > std::numeric_limits<std::uint64_t>::max())
        throw std::overflow_error("operation count exceeds uint64_t");
    return static_cast<std::uint64_t>(value);
}

struct ResidueResult {
    std::vector<std::uint64_t> coefficients;
    double seconds = 0;
};

ResidueResult compute(const Layout& layout, const TargetJobs& jobs,
                      std::uint64_t prime, int thread_count) {
    const int n = layout.n();
    const Montgomery mod(prime);
    std::vector<std::uint64_t> values(layout.entries(), 0);

    const auto row_ptr = [&](int ell, int a, int q) {
        return values.data() + layout.offset(ell, a, q);
    };

    const auto value_at = [&](int ell, int a, int q, int d) {
        const int support = a == 0 ? q + 1 : a + q;
        if (d < 0 || d >= support) return std::uint64_t{0};
        if (a == 0) return row_ptr(ell, 0, q - d)[0];
        if (d < a) return row_ptr(ell, a, q)[d];
        return row_ptr(ell, a, q - (d - a + 1))[a - 1];
    };

    const auto add_row = [&](std::uint64_t* target,
                             const std::uint64_t* source, int length) {
        for (int d = 0; d < length; ++d)
            target[d] = mod.add(target[d], source[d]);
    };

    const auto started = std::chrono::steady_clock::now();

    // Every direct source of a weight-w row has lower weight.  Split factors
    // have weights lower than w as well.  Thus the rows inside each of the
    // following three same-weight phases are mutually independent.
#pragma omp parallel num_threads(thread_count)
    {
        std::vector<std::uint64_t> prefix(n + 1, 0);
        for (int weight = 1; weight <= n; ++weight) {
            // E term: one independent diagonal scan for each ell.
#pragma omp for schedule(dynamic, 1)
            for (int ell = 1; ell <= weight; ++ell) {
                const int s = weight - ell;
                std::fill(prefix.begin(), prefix.begin() + s, 0);
                for (int a = 0; a <= s; ++a) {
                    const int q = s - a;
                    std::uint64_t* target = row_ptr(ell, a, q);
                    if (a != 0) add_row(target, prefix.data(), a);
                    if (a != s) {
                        const int source_support = a == 0 ? q : a + q - 1;
                        for (int d = 0; d < source_support; ++d)
                            prefix[d] = mod.add(
                                prefix[d], value_at(ell, a, q - 1, d));
                    }
                }
            }

            // J term: one independent q scan for each first-coordinate drop.
#pragma omp for schedule(dynamic, 1)
            for (int a = 0; a < weight; ++a) {
                const int t = weight - a;
                std::fill(prefix.begin(), prefix.begin() + weight, 0);
                for (int q = 0; q < t; ++q) {
                    const int ell = t - q;
                    std::uint64_t* target = row_ptr(ell, a, q);
                    add_row(target, prefix.data(), std::max(1, a));
                    if (q + 1 < t) {
                        const int source_support = a == 0 ? q + 1 : a + q;
                        for (int d = 0; d < source_support; ++d)
                            prefix[d] = mod.add(
                                prefix[d], value_at(ell - 1, a, q, d));
                    }
                }
            }

            // Endpoint and split terms.  Dynamic row scheduling is important:
            // split work varies strongly with ell and a.
            const std::int64_t first =
                static_cast<std::int64_t>(jobs.weight_begin[weight]);
            const std::int64_t last =
                static_cast<std::int64_t>(jobs.weight_begin[weight + 1]);
#pragma omp for schedule(dynamic, 1)
            for (std::int64_t job = first; job < last; ++job) {
                const int ell = jobs.ell[job];
                const int a = jobs.a[job];
                const int q = weight - ell - a;
                const int target_length = std::max(1, a);
                std::uint64_t* target = row_ptr(ell, a, q);

                if (ell == 1) {
                    if (a == 0 && q == 0)
                        target[0] = mod.add(target[0], mod.one);
                } else {
                    for (int d = 0; d < target_length; ++d)
                        target[d] = mod.add(
                            target[d],
                            mod.twice(value_at(ell - 1, a, q, d)));
                }

                for (int left_ell = 1; left_ell < ell - 1; ++left_ell) {
                    const int right_ell = ell - 1 - left_ell;
                    for (int left_drop = 0; left_drop <= a; ++left_drop) {
                        const int right_drop = a - left_drop;
                        const int left_support = left_drop == 0
                            ? q + 1 : left_drop + q;
                        for (int middle = 0; middle < left_support; ++middle) {
                            const std::uint64_t multiplicity = value_at(
                                left_ell, left_drop, q, middle);
                            if (multiplicity == 0) continue;
                            const int right_support = right_drop == 0
                                ? middle + 1 : right_drop + middle;
                            const int output_length =
                                std::min(target_length, right_support);
                            for (int d = 0; d < output_length; ++d) {
                                target[d] = mod.add(
                                    target[d],
                                    mod.multiply(
                                        multiplicity,
                                        value_at(right_ell, right_drop,
                                                 middle, d)));
                            }
                        }
                    }
                }
            }
        }
    }

    // The empty-stack table is lower order (O(N^5)).  For a fixed mass its
    // entries are independent: every right-hand-side control has smaller
    // mass, so the p loop can be shared as well.
    const int side = n + 1;
    std::vector<std::uint64_t> empty(
        static_cast<std::size_t>(side) * side, 0);
    const auto empty_at = [&](int p, int q) -> std::uint64_t& {
        return empty[static_cast<std::size_t>(p) * side + q];
    };
    empty_at(0, 0) = mod.one;
#pragma omp parallel num_threads(thread_count)
    {
        for (int mass = 1; mass <= n; ++mass) {
#pragma omp for schedule(dynamic, 1)
            for (int p = 0; p <= mass; ++p) {
                const int q = mass - p;
                std::uint64_t value = 0;
                for (int h = 0; h < p; ++h)
                    value = mod.add(value, empty_at(h, mass - h - 1));
                for (int r = 0; r < q; ++r) {
                    const int ell = q - r - 1;
                    if (ell == 0) {
                        value = mod.add(value, empty_at(p, r));
                        continue;
                    }
                    for (int c = 0; c <= p; ++c) {
                        const int drop = p - c;
                        const int support = drop == 0 ? r + 1 : drop + r;
                        for (int d = 0; d < support; ++d) {
                            value = mod.add(
                                value,
                                mod.multiply(value_at(ell, drop, r, d),
                                             empty_at(c, d)));
                        }
                    }
                }
                empty_at(p, q) = value;
            }
        }
    }

    ResidueResult result;
    result.coefficients.resize(n + 1);
    for (int degree = 0; degree <= n; ++degree)
        result.coefficients[degree] =
            mod.from_montgomery(empty_at(degree, 0));
    result.seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - started).count();
    return result;
}

int parse_nonnegative(const std::string& text, const char* name,
                      int maximum) {
    try {
        std::size_t used = 0;
        const long long value = std::stoll(text, &used);
        if (used != text.size() || value < 0 || value > maximum)
            throw std::invalid_argument("range");
        return static_cast<int>(value);
    } catch (...) {
        throw std::invalid_argument(std::string("invalid ") + name + ": " + text);
    }
}

std::uint64_t parse_prime(const std::string& text) {
    try {
        std::size_t used = 0;
        const unsigned long long value = std::stoull(text, &used);
        if (used != text.size() || value >= (1ULL << 62) || !is_prime(value))
            throw std::invalid_argument("range");
        return static_cast<std::uint64_t>(value);
    } catch (...) {
        throw std::invalid_argument(
            "invalid prime (must be prime and smaller than 2^62): " + text);
    }
}

struct Options {
    int max_n = 30;
    int threads = 0;
    std::uint64_t prime = default_prime;
    std::string output;
};

Options parse_options(int argc, char** argv) {
    Options options;
    bool have_n = false;
    for (int i = 1; i < argc; ++i) {
        const std::string argument = argv[i];
        if (argument == "--threads" && i + 1 < argc) {
            options.threads = parse_nonnegative(argv[++i], "thread count", 1024);
        } else if (argument == "--prime" && i + 1 < argc) {
            options.prime = parse_prime(argv[++i]);
        } else if (argument == "--output" && i + 1 < argc) {
            options.output = argv[++i];
        } else if (!argument.empty() && argument[0] != '-' && !have_n) {
            options.max_n = parse_nonnegative(argument, "N", 1000);
            have_n = true;
        } else {
            throw std::invalid_argument(
                "usage: av12453_scalar_residue_parallel [N] [--prime P] "
                "[--threads K] [--output FILE]");
        }
    }
    if (options.threads == 0) options.threads = omp_get_max_threads();
    if (options.threads < 1)
        throw std::invalid_argument("thread count must be positive");
    return options;
}

}  // namespace

int main(int argc, char** argv) {
    std::string temporary_output;
    try {
        const Options options = parse_options(argc, argv);
        const Layout layout(options.max_n);
        const TargetJobs jobs(options.max_n);

        std::cerr << "# N=" << options.max_n
                  << " rows=" << jobs.ell.size()
                  << " entries=" << layout.entries()
                  << " modulus=" << options.prime
                  << " threads=" << options.threads << '\n';

        const ResidueResult result = compute(
            layout, jobs, options.prime, options.threads);

        std::ostream* output = &std::cout;
        std::ofstream file;
        if (!options.output.empty()) {
            const auto nonce = std::chrono::steady_clock::now()
                                   .time_since_epoch().count();
            temporary_output = options.output + ".tmp." + std::to_string(nonce);
            file.open(temporary_output, std::ios::out | std::ios::trunc);
            if (!file)
                throw std::runtime_error("cannot open temporary output file");
            output = &file;
        }
        for (int degree = 0; degree <= options.max_n; ++degree)
            *output << degree << ' ' << result.coefficients[degree] << '\n';
        output->flush();
        if (!*output) throw std::runtime_error("failed while writing output");
        if (file.is_open()) {
            file.close();
            if (!file)
                throw std::runtime_error("failed while closing output file");
            if (std::rename(temporary_output.c_str(), options.output.c_str()) != 0)
                throw std::runtime_error("cannot install completed output file");
            temporary_output.clear();
        }

        const int n = options.max_n;
        const std::uint64_t split_madds =
            choose(n, 3) + 3 * choose(n, 4) + 6 * choose(n, 5) +
            8 * choose(n, 6) + 4 * choose(n, 7);
        const std::uint64_t empty_madds =
            choose(n, 2) + 3 * choose(n, 3) + 4 * choose(n, 4) +
            2 * choose(n, 5);
        std::cerr << "# seconds=" << std::fixed << std::setprecision(3)
                  << result.seconds
                  << " split_madds=" << split_madds
                  << " empty_madds=" << empty_madds << '\n';
        return 0;
    } catch (const std::exception& error) {
        if (!temporary_output.empty()) std::remove(temporary_output.c_str());
        std::cerr << "error: " << error.what() << '\n';
        return 2;
    }
}
