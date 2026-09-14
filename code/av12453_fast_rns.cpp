// AVX-512/RNS evaluation of the reduced Av(12453) transfer kernel.
//
// This is deliberately a separate implementation front-end.  It reuses the
// scalar program's Big integer, layout, primality, option-parsing, and CRT
// utilities, but evaluates eight independent primes in the lanes of one
// __m512i.  Compile on an AVX-512 target with OpenMP row parallelism:
//
//   g++ -O3 -DNDEBUG -march=native -std=c++20 -fopenmp
//       av12453_fast_rns.cpp -o av12453_fast_rns
//
// Every lane modulus is below 2^31 and Montgomery R is 2^32.  Thus, for
// canonical residues a,b < p, t=a*b is below R*p and
//
//   t + ((t * (-p^-1)) mod R) * p < 2*R*p < 2^64,
//
// so the packed reduction is exact without an inter-lane carry.

#define main av12453_embedded_scalar_main
#include "av12453_fast.cpp"
#undef main

#include <array>
#include <immintrin.h>
#include <omp.h>
#include <sstream>

namespace {

constexpr int rns_lanes = 8;

struct alignas(32) VecWord {
    __m256i value{};
};

inline __m512i load_word(const VecWord& word) {
    return _mm512_cvtepu32_epi64(word.value);
}

inline void store_word(VecWord& word, __m512i value) {
    word.value = _mm512_cvtepi64_epi32(value);
}

__m512i load_lanes(const std::array<std::uint64_t, rns_lanes>& lanes) {
    return _mm512_loadu_si512(lanes.data());
}

struct Montgomery8 {
    __m512i modulus;
    __m512i neg_inverse;
    __m512i r2;
    __m512i one;

    explicit Montgomery8(
        const std::array<std::uint32_t, rns_lanes>& primes) {
        std::array<std::uint64_t, rns_lanes> p_lanes{};
        std::array<std::uint64_t, rns_lanes> inverse_lanes{};
        std::array<std::uint64_t, rns_lanes> r2_lanes{};
        for (int lane = 0; lane < rns_lanes; ++lane) {
            const std::uint32_t p = primes[lane];
            if ((p & 1U) == 0 || p >= (1U << 31))
                throw std::invalid_argument("RNS modulus out of range");

            std::uint32_t inverse = 1;
            for (int iteration = 0; iteration < 5; ++iteration)
                inverse *= 2U - p * inverse;
            const std::uint32_t neg_inverse = 0U - inverse;
            const std::uint64_t r = (std::uint64_t{1} << 32) % p;

            p_lanes[lane] = p;
            inverse_lanes[lane] = neg_inverse;
            r2_lanes[lane] = r * r % p;
        }
        modulus = load_lanes(p_lanes);
        neg_inverse = load_lanes(inverse_lanes);
        r2 = load_lanes(r2_lanes);
        const __m512i ordinary_one = _mm512_set1_epi64(1);
        one = multiply(ordinary_one, r2);
    }

    __m512i multiply(__m512i a, __m512i b) const {
        // _mm512_mul_epu32 multiplies the low 32 bits of every 64-bit lane.
        const __m512i product = _mm512_mul_epu32(a, b);
        const __m512i multiplier =
            _mm512_mul_epu32(product, neg_inverse);
        const __m512i correction =
            _mm512_mul_epu32(multiplier, modulus);
        __m512i result = _mm512_srli_epi64(
            _mm512_add_epi64(product, correction), 32);
        const __mmask8 reduce = _mm512_cmp_epu64_mask(
            result, modulus, _MM_CMPINT_NLT);
        return _mm512_mask_sub_epi64(result, reduce, result, modulus);
    }

    __m512i add(__m512i a, __m512i b) const {
        __m512i sum = _mm512_add_epi64(a, b);
        const __mmask8 reduce = _mm512_cmp_epu64_mask(
            sum, modulus, _MM_CMPINT_NLT);
        return _mm512_mask_sub_epi64(sum, reduce, sum, modulus);
    }

    __m512i twice(__m512i a) const { return add(a, a); }

    __m512i from_montgomery(__m512i value) const {
        return multiply(value, _mm512_set1_epi64(1));
    }
};

struct PackResult {
    std::array<std::uint32_t, rns_lanes> primes{};
    std::array<std::vector<std::uint64_t>, rns_lanes> coefficients;
    double seconds = 0;
};

std::uint64_t choose_small(int n, int k) {
    if (k < 0 || n < k) return 0;
    k = std::min(k, n - k);
    unsigned __int128 result = 1;
    for (int j = 1; j <= k; ++j) {
        result = result * static_cast<unsigned>(n - k + j)
               / static_cast<unsigned>(j);
    }
    if (result > std::numeric_limits<std::uint64_t>::max())
        throw std::overflow_error("operation count is too large");
    return static_cast<std::uint64_t>(result);
}

std::uint64_t split_operation_count(int n) {
    return choose_small(n, 3) + 3 * choose_small(n, 4)
         + 6 * choose_small(n, 5) + 8 * choose_small(n, 6)
         + 4 * choose_small(n, 7);
}

std::uint64_t empty_operation_count(int n) {
    return choose_small(n, 2) + 3 * choose_small(n, 3)
         + 4 * choose_small(n, 4) + 2 * choose_small(n, 5);
}

PackResult run_pack(
    const Layout& layout,
    const std::array<std::uint32_t, rns_lanes>& primes,
    int thread_count) {
    const int n = layout.n();
    const Montgomery8 mod(primes);
    std::vector<VecWord> values(layout.entries());
    std::vector<VecWord> prefix(n + 1);
    const int side = n + 1;
    std::vector<std::uint64_t> boundary_base(
        static_cast<std::size_t>(side) * side, 0);
    std::uint64_t boundary_entries = 0;
    for (int ell = 1; ell <= n; ++ell) {
        for (int a = 0; a + ell <= n; ++a) {
            boundary_base[static_cast<std::size_t>(ell) * side + a] =
                boundary_entries;
            boundary_entries += static_cast<std::uint64_t>(n - ell - a + 1);
        }
    }
    std::vector<VecWord> boundary(boundary_entries);

    const auto row_ptr = [&](int ell, int a, int q) {
        const RowInfo& info = layout.row(ell, a, q);
        return values.data() + info.offset;
    };

    const auto boundary_at = [&](int ell, int a, int q) -> VecWord& {
        return boundary[
            boundary_base[static_cast<std::size_t>(ell) * side + a] + q];
    };

    const auto value_at = [&](int ell, int a, int q, int d) {
        const int support = a == 0 ? q + 1 : a + q;
        if (d < 0 || d >= support) return _mm512_setzero_si512();
        if (a == 0)
            return load_word(boundary_at(ell, 0, q - d));
        if (d < a) return load_word(row_ptr(ell, a, q)[d]);
        return load_word(boundary_at(ell, a, q - (d - a + 1)));
    };

    const auto add_row = [&](VecWord* target,
                             const VecWord* source,
                             int length) {
        for (int d = 0; d < length; ++d)
            store_word(target[d], mod.add(load_word(target[d]),
                                          load_word(source[d])));
    };

    const auto started = std::chrono::steady_clock::now();
    for (int weight = 1; weight <= n; ++weight) {
        // The E and J scans are lower order than the split.  Keeping them
        // serial also keeps their diagonal prefix buffer simple.
        for (int ell = 1; ell <= weight; ++ell) {
            const int s = weight - ell;
            for (int d = 0; d < s; ++d)
                prefix[d].value = _mm256_setzero_si256();
            for (int a = 0; a <= s; ++a) {
                const int q = s - a;
                VecWord* target = row_ptr(ell, a, q);
                if (a != 0) add_row(target, prefix.data(), a);
                if (a != s) {
                    const int source_support = a == 0 ? q : a + q - 1;
                    for (int d = 0; d < source_support; ++d) {
                        store_word(prefix[d], mod.add(
                            load_word(prefix[d]),
                            value_at(ell, a, q - 1, d)));
                    }
                }
            }
        }

        for (int a = 0; a < weight; ++a) {
            const int t = weight - a;
            for (int d = 0; d < weight; ++d)
                prefix[d].value = _mm256_setzero_si256();
            for (int q = 0; q < t; ++q) {
                const int ell = t - q;
                VecWord* target = row_ptr(ell, a, q);
                const int target_length = std::max(1, a);
                add_row(target, prefix.data(), target_length);
                if (q + 1 < t) {
                    const int source_support = a == 0 ? q + 1 : a + q;
                    for (int d = 0; d < source_support; ++d) {
                        store_word(prefix[d], mod.add(
                            load_word(prefix[d]),
                            value_at(ell - 1, a, q, d)));
                    }
                }
            }
        }

        // Every target row at this weight reads only lower weights.  Encode
        // the triangular (ell,a) set as a compact task list and dynamically
        // schedule rows to smooth the strongly varying split cost.
        std::vector<std::pair<int, int>> tasks;
        tasks.reserve(static_cast<std::size_t>(weight) * (weight + 1) / 2);
        for (int ell = 1; ell <= weight; ++ell) {
            const int remainder = weight - ell;
            for (int a = 0; a <= remainder; ++a)
                tasks.emplace_back(ell, a);
        }

#pragma omp parallel for schedule(dynamic, 1) num_threads(thread_count)
        for (std::ptrdiff_t task_index = 0;
             task_index < static_cast<std::ptrdiff_t>(tasks.size());
             ++task_index) {
            const int ell = tasks[task_index].first;
            const int a = tasks[task_index].second;
            const int q = weight - ell - a;
            const RowInfo& target_info = layout.row(ell, a, q);
            VecWord* target = values.data() + target_info.offset;
            const int target_length = std::max(1, a);

            if (ell == 1) {
                if (a == 0 && q == 0)
                    store_word(target[0],
                               mod.add(load_word(target[0]), mod.one));
            } else {
                for (int d = 0; d < target_length; ++d) {
                    store_word(target[d], mod.add(
                        load_word(target[d]),
                        mod.twice(value_at(ell - 1, a, q, d))));
                }
            }

            for (int left_ell = 1; left_ell < ell - 1; ++left_ell) {
                const int right_ell = ell - 1 - left_ell;
                for (int left_drop = 0; left_drop <= a; ++left_drop) {
                    const int right_drop = a - left_drop;
                    const int left_support = left_drop == 0
                        ? q + 1 : left_drop + q;
                    for (int middle = 0; middle < left_support; ++middle) {
                        const __m512i multiplicity = value_at(
                            left_ell, left_drop, q, middle);
                        const int right_support = right_drop == 0
                            ? middle + 1 : right_drop + middle;
                        const int output_length = std::min<int>(
                            target_length, right_support);
                        const int contiguous_length = right_drop == 0
                            ? 0 : std::min(output_length, right_drop);
                        const VecWord* right_row = right_drop == 0
                            ? nullptr
                            : row_ptr(right_ell, right_drop, middle);
                        for (int d = 0; d < contiguous_length; ++d) {
                            store_word(target[d], mod.add(
                                load_word(target[d]),
                                mod.multiply(
                                    multiplicity,
                                    load_word(right_row[d]))));
                        }
                        for (int d = contiguous_length;
                             d < output_length; ++d) {
                            const int shifted_q = right_drop == 0
                                ? middle - d
                                : middle - (d - right_drop + 1);
                            store_word(target[d], mod.add(
                                load_word(target[d]),
                                mod.multiply(
                                    multiplicity,
                                    load_word(boundary_at(
                                        right_ell, right_drop,
                                        shifted_q)))));
                        }
                    }
                }
            }
            boundary_at(ell, a, q) = target[target_length - 1];
        }
    }

    std::vector<VecWord> empty(static_cast<std::size_t>(side) * side);
    const auto empty_at = [&](int p, int q) -> VecWord& {
        return empty[static_cast<std::size_t>(p) * side + q];
    };
    store_word(empty_at(0, 0), mod.one);
    for (int mass = 1; mass <= n; ++mass) {
        for (int p = 0; p <= mass; ++p) {
            const int q = mass - p;
            __m512i value = _mm512_setzero_si512();
            for (int h = 0; h < p; ++h)
                value = mod.add(value,
                                load_word(empty_at(h, mass - h - 1)));
            for (int r = 0; r < q; ++r) {
                const int ell = q - r - 1;
                if (ell == 0) {
                    value = mod.add(value, load_word(empty_at(p, r)));
                    continue;
                }
                for (int c = 0; c <= p; ++c) {
                    const int drop = p - c;
                    const int support = drop == 0 ? r + 1 : drop + r;
                    for (int d = 0; d < support; ++d) {
                        value = mod.add(
                            value,
                            mod.multiply(
                                value_at(ell, drop, r, d),
                                load_word(empty_at(c, d))));
                    }
                }
            }
            store_word(empty_at(p, q), value);
        }
    }

    PackResult result;
    result.primes = primes;
    for (auto& coefficients : result.coefficients)
        coefficients.resize(n + 1);
    for (int degree = 0; degree <= n; ++degree) {
        alignas(64) std::array<std::uint64_t, rns_lanes> lanes{};
        _mm512_store_si512(
            lanes.data(),
            mod.from_montgomery(load_word(empty_at(degree, 0))));
        for (int lane = 0; lane < rns_lanes; ++lane)
            result.coefficients[lane][degree] = lanes[lane];
    }
    result.seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - started).count();
    return result;
}

std::vector<std::uint32_t> select_rns_primes(int n) {
    Big coefficient_bound = 2;
    for (int k = 0; k < n; ++k) coefficient_bound.multiply(15);

    Big product = 1;
    std::vector<std::uint32_t> primes;
    std::uint64_t candidate = (std::uint64_t{1} << 31) - 1;
    while (product <= coefficient_bound || primes.size() % rns_lanes != 0) {
        while (!is_prime(candidate)) candidate -= 2;
        primes.push_back(static_cast<std::uint32_t>(candidate));
        product.multiply(candidate);
        candidate -= 2;
    }
    return primes;
}

std::string pack_prime_text(
    const std::array<std::uint32_t, rns_lanes>& primes) {
    std::ostringstream text;
    for (int lane = 0; lane < rns_lanes; ++lane) {
        if (lane) text << ',';
        text << primes[lane];
    }
    return text.str();
}

struct RnsOptions {
    int max_n = 30;
    int threads = 0;
    std::string output;
    bool residues_only = false;
    int pack_index = -1;
};

RnsOptions parse_rns_options(int argc, char** argv) {
    RnsOptions options;
    bool have_n = false;
    for (int i = 1; i < argc; ++i) {
        const std::string argument = argv[i];
        if (argument == "--threads" && i + 1 < argc) {
            options.threads = parse_nonnegative(argv[++i], "thread count");
        } else if (argument == "--output" && i + 1 < argc) {
            options.output = argv[++i];
        } else if (argument == "--residues-only") {
            options.residues_only = true;
        } else if (argument == "--pack-index" && i + 1 < argc) {
            options.pack_index = parse_nonnegative(argv[++i], "pack index");
        } else if (!argument.empty() && argument[0] != '-' && !have_n) {
            options.max_n = parse_nonnegative(argument, "N");
            have_n = true;
        } else {
            throw std::invalid_argument(
                "usage: av12453_fast_rns [N] [--threads K] [--output FILE] "
                "[--residues-only] [--pack-index K]");
        }
    }
    if (options.threads == 0) {
        const unsigned available = std::thread::hardware_concurrency();
        options.threads = available == 0 ? 1 : static_cast<int>(available);
    }
    if (options.pack_index >= 0 && !options.residues_only)
        throw std::invalid_argument(
            "--pack-index requires --residues-only");
    return options;
}

}  // namespace

#ifndef AV12453_RNS_NO_MAIN
int main(int argc, char** argv) {
    std::string temporary_output;
    try {
        const RnsOptions options = parse_rns_options(argc, argv);
        const int n = options.max_n;
        const Layout layout(n);
        const std::vector<std::uint32_t> primes = select_rns_primes(n);
        const int pack_count = static_cast<int>(primes.size()) / rns_lanes;
        if (options.pack_index >= pack_count)
            throw std::invalid_argument("pack index is outside the available range");
        const int first_pack = options.pack_index < 0 ? 0 : options.pack_index;
        const int past_last_pack = options.pack_index < 0
            ? pack_count : options.pack_index + 1;
        const int thread_count = std::max(1, options.threads);
        omp_set_dynamic(0);

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

        std::cerr << "# RNS N=" << n
                  << " rows="
                  << (static_cast<std::uint64_t>(n) * (n + 1) * (n + 2) / 6)
                  << " entries=" << layout.entries()
                  << " primes=" << primes.size()
                  << " packs=" << pack_count
                  << " selected_packs=" << first_pack << ".."
                  << (past_last_pack - 1)
                  << " threads=" << thread_count << '\n';

        const auto all_started = std::chrono::steady_clock::now();
        std::vector<PrimeResult> scalar_results;
        scalar_results.reserve(primes.size());
        for (int pack_index = first_pack;
             pack_index < past_last_pack; ++pack_index) {
            std::array<std::uint32_t, rns_lanes> pack_primes{};
            for (int lane = 0; lane < rns_lanes; ++lane)
                pack_primes[lane] = primes[pack_index * rns_lanes + lane];

            PackResult pack = run_pack(layout, pack_primes, thread_count);
            std::cerr << "# pack=" << pack_index
                      << " primes=" << pack_prime_text(pack_primes)
                      << " seconds=" << std::fixed << std::setprecision(3)
                      << pack.seconds
                      << " split_madds=" << split_operation_count(n)
                      << " empty_madds=" << empty_operation_count(n) << '\n';
            for (int lane = 0; lane < rns_lanes; ++lane) {
                PrimeResult result;
                result.prime = pack.primes[lane];
                result.coefficients = std::move(pack.coefficients[lane]);
                result.seconds = pack.seconds;
                result.split_multiply_adds = split_operation_count(n);
                result.empty_multiply_adds = empty_operation_count(n);
                scalar_results.push_back(std::move(result));
            }
        }

        if (options.residues_only) {
            for (const PrimeResult& result : scalar_results) {
                *output << "# modulus " << result.prime << '\n';
                for (int degree = 0; degree <= n; ++degree)
                    *output << degree << ' '
                            << result.coefficients[degree] << '\n';
            }
        } else {
            const std::vector<Big> coefficients = reconstruct(scalar_results, n);
            for (int degree = 0; degree <= n; ++degree)
                *output << degree << ' ' << coefficients[degree] << '\n';
        }

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
#endif
