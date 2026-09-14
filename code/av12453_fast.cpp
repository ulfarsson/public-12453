// Fast exact enumeration of Av(12453) by reduced transfer kernels.
//
// Compile:
//   g++ -O3 -DNDEBUG -march=native -std=c++20 -pthread av12453_fast.cpp -o
//   av12453_fast
// Run:
//   ./av12453_fast 100
//   ./av12453_fast 100 --threads 7 --output av12453_terms_0_100.txt
//
// The recurrence is the first-coordinate Toeplitz quotient implemented in
// av12453_reduced.py.  This version uses the exact support of every row,
// contiguous storage of the second-coordinate Toeplitz boundary, prefix scans
// for the two linear terms, and independent Montgomery-modular computations.
// CRT reconstruction is exact:
// enough distinct primes are used that their product exceeds 2*15^N, a proved
// upper bound for every requested coefficient.

#include <algorithm>
#include <atomic>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <mutex>
#include <numeric>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>

namespace {

// A nonnegative base-10^9 integer.  Large integers are needed for the CRT
// bound, modulus product, and O(N) final values, not for the transfer table.
class Big {
  public:
    static constexpr std::uint32_t base = 1000000000U;

    Big(std::uint64_t value = 0) {
        while (value != 0) {
            digits_.push_back(static_cast<std::uint32_t>(value % base));
            value /= base;
        }
    }

    Big& multiply(std::uint64_t factor) {
        if (factor == 0 || digits_.empty()) {
            digits_.clear();
            return *this;
        }
        unsigned __int128 carry = 0;
        for (std::uint32_t& digit : digits_) {
            const unsigned __int128 value =
                static_cast<unsigned __int128>(digit) * factor + carry;
            digit = static_cast<std::uint32_t>(value % base);
            carry = value / base;
        }
        while (carry != 0) {
            digits_.push_back(static_cast<std::uint32_t>(carry % base));
            carry /= base;
        }
        return *this;
    }

    void add_scaled(const Big& value, std::uint64_t scale) {
        if (scale == 0 || value.digits_.empty()) return;
        if (digits_.size() < value.digits_.size())
            digits_.resize(value.digits_.size(), 0);
        unsigned __int128 carry = 0;
        std::size_t position = 0;
        for (; position < value.digits_.size(); ++position) {
            const unsigned __int128 sum =
                static_cast<unsigned __int128>(value.digits_[position]) * scale
                + digits_[position] + carry;
            digits_[position] = static_cast<std::uint32_t>(sum % base);
            carry = sum / base;
        }
        while (carry != 0) {
            if (position == digits_.size()) digits_.push_back(0);
            const unsigned __int128 sum = digits_[position] + carry;
            digits_[position] = static_cast<std::uint32_t>(sum % base);
            carry = sum / base;
            ++position;
        }
    }

    std::uint64_t modulo(std::uint64_t modulus) const {
        unsigned __int128 remainder = 0;
        for (std::size_t position = digits_.size(); position-- > 0;)
            remainder = (remainder * base + digits_[position]) % modulus;
        return static_cast<std::uint64_t>(remainder);
    }

    friend bool operator<=(const Big& left, const Big& right) {
        if (left.digits_.size() != right.digits_.size())
            return left.digits_.size() < right.digits_.size();
        for (std::size_t position = left.digits_.size(); position-- > 0;) {
            if (left.digits_[position] != right.digits_[position])
                return left.digits_[position] < right.digits_[position];
        }
        return true;
    }

    friend std::ostream& operator<<(std::ostream& out, const Big& value) {
        if (value.digits_.empty()) return out << '0';
        out << value.digits_.back();
        for (std::size_t position = value.digits_.size() - 1;
             position-- > 0;)
            out << std::setw(9) << std::setfill('0')
                << value.digits_[position];
        out << std::setfill(' ');
        return out;
    }

  private:
    std::vector<std::uint32_t> digits_;
};

struct RowInfo {
    std::uint64_t offset = 0;
};

class Layout {
  public:
    explicit Layout(int n) : n_(n), side_(n + 1), rows_(cube_size()) {
        std::uint64_t offset = 0;
        for (int weight = 1; weight <= n_; ++weight) {
            for (int ell = 1; ell <= weight; ++ell) {
                const int remainder = weight - ell;
                for (int a = 0; a <= remainder; ++a) {
                    const int q = remainder - a;
                    // The partial second-coordinate Toeplitz law is
                    // R(l,a,q+1,d+1)=R(l,a,q,d) for d>=a-1.  Hence a row is
                    // determined by d=0,...,a-1 (only d=0 when a=0).
                    const int length = std::max(1, a);
                    rows_[index(ell, a, q)] = {offset};
                    offset += static_cast<std::uint64_t>(length);
                }
            }
        }
        entries_ = offset;
    }

    int n() const { return n_; }
    std::uint64_t entries() const { return entries_; }

    const RowInfo& row(int ell, int a, int q) const {
        return rows_[index(ell, a, q)];
    }

  private:
    int n_;
    std::size_t side_;
    std::vector<RowInfo> rows_;
    std::uint64_t entries_ = 0;

    std::size_t cube_size() const {
        const std::size_t s = side_;
        if (s != 0 && s > std::numeric_limits<std::size_t>::max() / s / s)
            throw std::overflow_error("layout is too large");
        return s * s * s;
    }

    std::size_t index(int ell, int a, int q) const {
        return (static_cast<std::size_t>(ell) * side_ + a) * side_ + q;
    }
};

// Deterministic Miller--Rabin for unsigned 64-bit integers.
std::uint64_t pow_mod(std::uint64_t a, std::uint64_t e, std::uint64_t mod) {
    std::uint64_t result = 1;
    while (e != 0) {
        if (e & 1)
            result = static_cast<std::uint64_t>(
                static_cast<unsigned __int128>(result) * a % mod);
        a = static_cast<std::uint64_t>(
            static_cast<unsigned __int128>(a) * a % mod);
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
    // This base set is deterministic on [0,2^64).
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
            throw std::invalid_argument("Montgomery modulus out of range");
        // Newton iteration for p^{-1} modulo 2^64.
        std::uint64_t inverse = 1;
        for (int i = 0; i < 6; ++i) inverse *= 2 - p * inverse;
        neg_inverse = 0 - inverse;
        const std::uint64_t r = static_cast<std::uint64_t>(
            (static_cast<unsigned __int128>(1) << 64) % p);
        r2 = static_cast<std::uint64_t>(
            static_cast<unsigned __int128>(r) * r % p);
        one = to_montgomery(1);
    }

    std::uint64_t multiply(std::uint64_t a, std::uint64_t b) const {
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

    std::uint64_t add(std::uint64_t a, std::uint64_t b) const {
        const std::uint64_t sum = a + b;
        return sum >= modulus ? sum - modulus : sum;
    }

    std::uint64_t twice(std::uint64_t a) const { return add(a, a); }

    std::uint64_t to_montgomery(std::uint64_t value) const {
        return multiply(value % modulus, r2);
    }

    std::uint64_t from_montgomery(std::uint64_t value) const {
        return multiply(value, 1);
    }
};

struct PrimeResult {
    std::uint64_t prime = 0;
    std::vector<std::uint64_t> coefficients;
    double seconds = 0;
    std::uint64_t split_multiply_adds = 0;
    std::uint64_t empty_multiply_adds = 0;
};

PrimeResult run_prime(const Layout& layout, std::uint64_t prime) {
    const int n = layout.n();
    const Montgomery mod(prime);
    std::vector<std::uint64_t> values(layout.entries(), 0);
    std::vector<std::uint64_t> prefix(n + 1, 0);
    std::uint64_t split_multiply_adds = 0;
    std::uint64_t empty_multiply_adds = 0;

    const auto row_ptr = [&](int ell, int a, int q) {
        const RowInfo& info = layout.row(ell, a, q);
        return values.data() + info.offset;
    };

    const auto value_at = [&](int ell, int a, int q, int d) {
        const int support = a == 0 ? q + 1 : a + q;
        if (d < 0 || d >= support) return std::uint64_t{0};
        if (a == 0) {
            // Shift (q,d) down the Toeplitz diagonal to column zero.
            return row_ptr(ell, 0, q - d)[0];
        }
        if (d < a) return row_ptr(ell, a, q)[d];
        // Shift to the last stored boundary column a-1.
        return row_ptr(ell, a, q - (d - a + 1))[a - 1];
    };

    const auto add_row = [&](std::uint64_t* target,
                             const std::uint64_t* source,
                             int length) {
        for (int d = 0; d < length; ++d)
            target[d] = mod.add(target[d], source[d]);
    };

    const auto started = std::chrono::steady_clock::now();
    for (int weight = 1; weight <= n; ++weight) {
        // E term.  For fixed ell and s=a+q, scan a along the diagonal:
        //   E(a+1)=E(a)+R_ell(a,s-a-1).
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

        // J term.  For fixed a and t=ell+q, scan q:
        //   J(q+1)=J(q)+R_{t-q-1}(a,q).
        for (int a = 0; a < weight; ++a) {
            const int t = weight - a;
            std::fill(prefix.begin(), prefix.begin() + weight, 0);
            for (int q = 0; q < t; ++q) {
                const int ell = t - q;
                std::uint64_t* target = row_ptr(ell, a, q);
                const int target_length = std::max(1, a);
                add_row(target, prefix.data(), target_length);
                if (q + 1 < t) {
                    const int source_support = a == 0 ? q + 1 : a + q;
                    for (int d = 0; d < source_support; ++d)
                        prefix[d] = mod.add(
                            prefix[d], value_at(ell - 1, a, q, d));
                }
            }
        }

        // Endpoint, double-endpoint, and split terms.
        for (int ell = 1; ell <= weight; ++ell) {
            const int remainder = weight - ell;
            for (int a = 0; a <= remainder; ++a) {
                const int q = remainder - a;
                const RowInfo& target_info = layout.row(ell, a, q);
                std::uint64_t* target = values.data() + target_info.offset;
                const int target_length = std::max(1, a);

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
                        for (int middle = 0;
                             middle < left_support; ++middle) {
                            const std::uint64_t multiplicity = value_at(
                                left_ell, left_drop, q, middle);
                            if (multiplicity == 0) continue;
                            const int right_support = right_drop == 0
                                ? middle + 1 : right_drop + middle;
                            const int output_length = std::min<int>(
                                target_length, right_support);
                            for (int d = 0; d < output_length; ++d) {
                                target[d] = mod.add(
                                    target[d],
                                    mod.multiply(
                                        multiplicity,
                                        value_at(right_ell, right_drop,
                                                 middle, d)));
                            }
                            split_multiply_adds += output_length;
                        }
                    }
                }
            }
        }
    }

    // Empty-stack values g(p,q), stored in a square array for cheap indexing.
    const int side = n + 1;
    std::vector<std::uint64_t> empty(
        static_cast<std::size_t>(side) * side, 0);
    const auto empty_at = [&](int p, int q) -> std::uint64_t& {
        return empty[static_cast<std::size_t>(p) * side + q];
    };
    empty_at(0, 0) = mod.one;
    for (int mass = 1; mass <= n; ++mass) {
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
                            mod.multiply(
                                value_at(ell, drop, r, d), empty_at(c, d)));
                        ++empty_multiply_adds;
                    }
                }
            }
            empty_at(p, q) = value;
        }
    }

    PrimeResult result;
    result.prime = prime;
    result.coefficients.resize(n + 1);
    for (int degree = 0; degree <= n; ++degree)
        result.coefficients[degree] =
            mod.from_montgomery(empty_at(degree, 0));
    result.seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - started).count();
    result.split_multiply_adds = split_multiply_adds;
    result.empty_multiply_adds = empty_multiply_adds;
    return result;
}

std::uint64_t inverse_mod(std::uint64_t value, std::uint64_t prime) {
    return pow_mod(value, prime - 2, prime);
}

std::vector<Big> reconstruct(
    const std::vector<PrimeResult>& results, int n) {
    std::vector<Big> coefficients(n + 1, Big(0));
    Big product = 1;
    for (const PrimeResult& result : results) {
        const std::uint64_t p = result.prime;
        const std::uint64_t product_mod = product.modulo(p);
        const std::uint64_t product_inverse = inverse_mod(product_mod, p);
        for (int degree = 0; degree <= n; ++degree) {
            const std::uint64_t current = coefficients[degree].modulo(p);
            const std::uint64_t difference =
                result.coefficients[degree] >= current
                    ? result.coefficients[degree] - current
                    : result.coefficients[degree] + p - current;
            const std::uint64_t correction = static_cast<std::uint64_t>(
                static_cast<unsigned __int128>(difference) * product_inverse
                % p);
            coefficients[degree].add_scaled(product, correction);
        }
        product.multiply(p);
    }
    return coefficients;
}

int parse_nonnegative(const std::string& text, const char* name) {
    try {
        std::size_t used = 0;
        const long long value = std::stoll(text, &used);
        if (used != text.size() || value < 0 || value > 1000)
            throw std::invalid_argument("range");
        return static_cast<int>(value);
    } catch (...) {
        throw std::invalid_argument(std::string("invalid ") + name + ": " + text);
    }
}

struct Options {
    int max_n = 30;
    int threads = 0;
    std::string output;
    bool residues_only = false;
};

Options parse_options(int argc, char** argv) {
    Options options;
    bool have_n = false;
    for (int i = 1; i < argc; ++i) {
        const std::string argument = argv[i];
        if (argument == "--threads" && i + 1 < argc) {
            options.threads = parse_nonnegative(argv[++i], "thread count");
        } else if (argument == "--output" && i + 1 < argc) {
            options.output = argv[++i];
        } else if (argument == "--residues-only") {
            options.residues_only = true;
        } else if (!argument.empty() && argument[0] != '-' && !have_n) {
            options.max_n = parse_nonnegative(argument, "N");
            have_n = true;
        } else {
            throw std::invalid_argument("usage: av12453_fast [N] [--threads K] "
                                        "[--output FILE] [--residues-only]");
        }
    }
    if (options.threads == 0) {
        const unsigned available = std::thread::hardware_concurrency();
        options.threads = available == 0 ? 1 : static_cast<int>(available);
    }
    return options;
}

}  // namespace

int main(int argc, char** argv) {
    std::string temporary_output;
    try {
        const Options options = parse_options(argc, argv);
        const int n = options.max_n;
        const Layout layout(n);

        // Reserve an output file before beginning an expensive run, without
        // replacing an existing result until the new file is complete.
        std::ostream* output = &std::cout;
        std::ofstream file;
        if (!options.output.empty()) {
            const auto nonce = std::chrono::steady_clock::now()
                                   .time_since_epoch().count();
            temporary_output = options.output + ".tmp." + std::to_string(nonce);
            file.open(temporary_output, std::ios::out | std::ios::trunc);
            if (!file) throw std::runtime_error("cannot open temporary output file");
            output = &file;
        }

        // Select distinct primes just below 2^61 until their product exceeds
        // 2*15^N.  This is a rigorous simultaneous reconstruction bound:
        // deleting the left-to-right minima leaves a 1342-avoider, and
        // Bona's generating function gives |Av_n(12453)| < 2*15^n.
        Big coefficient_bound = 2;
        for (int k = 0; k < n; ++k) coefficient_bound.multiply(15);
        Big prime_product = 1;
        std::vector<std::uint64_t> primes;
        std::uint64_t candidate = (1ULL << 61) - 1;
        while (prime_product <= coefficient_bound) {
            while (!is_prime(candidate)) candidate -= 2;
            primes.push_back(candidate);
            prime_product.multiply(candidate);
            candidate -= 2;
        }

        std::cerr << "# N=" << n << " rows="
                  << (static_cast<std::uint64_t>(n) * (n + 1) * (n + 2) / 6)
                  << " entries=" << layout.entries()
                  << " primes=" << primes.size()
                  << " threads=" << std::min<int>(options.threads, primes.size())
                  << '\n';

        const auto all_started = std::chrono::steady_clock::now();
        std::vector<PrimeResult> results(primes.size());
        std::atomic<std::size_t> next_prime{0};
        std::mutex progress_mutex;
        std::mutex exception_mutex;
        std::exception_ptr worker_exception;
        const int worker_count =
            std::max(1, std::min<int>(options.threads, primes.size()));
        std::vector<std::jthread> workers;
        workers.reserve(worker_count);
        for (int worker = 0; worker < worker_count; ++worker) {
            workers.emplace_back([&] {
                try {
                    for (;;) {
                        const std::size_t index = next_prime.fetch_add(1);
                        if (index >= primes.size()) break;
                        results[index] = run_prime(layout, primes[index]);
                        std::lock_guard<std::mutex> lock(progress_mutex);
                        std::cerr << "# prime=" << primes[index]
                                  << " seconds=" << std::fixed
                                  << std::setprecision(3)
                                  << results[index].seconds
                                  << " split_madds="
                                  << results[index].split_multiply_adds
                                  << " empty_madds="
                                  << results[index].empty_multiply_adds
                                  << '\n';
                    }
                } catch (...) {
                    std::lock_guard<std::mutex> lock(exception_mutex);
                    if (!worker_exception)
                        worker_exception = std::current_exception();
                }
            });
        }
        for (std::jthread& worker : workers) worker.join();
        if (worker_exception) std::rethrow_exception(worker_exception);

        if (options.residues_only) {
            for (std::size_t k = 0; k < results.size(); ++k) {
                *output << "# modulus " << results[k].prime << '\n';
                for (int degree = 0; degree <= n; ++degree)
                    *output << degree << ' '
                            << results[k].coefficients[degree] << '\n';
            }
        } else {
            const std::vector<Big> coefficients = reconstruct(results, n);
            for (int degree = 0; degree <= n; ++degree)
                *output << degree << ' ' << coefficients[degree] << '\n';
        }

        output->flush();
        if (!*output) throw std::runtime_error("failed while writing output");
        if (file.is_open()) {
            file.close();
            if (!file) throw std::runtime_error("failed while closing output file");
            if (std::rename(temporary_output.c_str(), options.output.c_str()) != 0)
                throw std::runtime_error("cannot install completed output file");
            temporary_output.clear();
        }

        const double total_seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - all_started).count();
        std::cerr << "# total_seconds=" << std::fixed << std::setprecision(3)
                  << total_seconds << '\n';
        return 0;
    } catch (const std::exception& error) {
        if (!temporary_output.empty()) std::remove(temporary_output.c_str());
        std::cerr << "error: " << error.what() << '\n';
        return 2;
    }
}
