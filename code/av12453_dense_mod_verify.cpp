// Independent dense modular verifier for av12453_fast.cpp.
//
// This deliberately evaluates the reduced recurrence literally: it stores
// every endpoint R_ell(a,q,d), uses neither second-coordinate compression nor
// prefix scans, and works modulo the Mersenne prime 2^61-1.  It is intended
// for validation, not for the production run through n=100.
//
// Compile:
//   g++ -O3 -DNDEBUG -march=native -std=c++20
//     av12453_dense_mod_verify.cpp -o av12453_dense_mod_verify
// Run:
//   ./av12453_dense_mod_verify 60 > dense_residues_60.txt

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <vector>

namespace {

constexpr std::uint64_t modulus = (1ULL << 61) - 1;

inline std::uint64_t add_mod(std::uint64_t a, std::uint64_t b) {
    std::uint64_t sum = a + b;
    sum = (sum & modulus) + (sum >> 61);
    return sum == modulus ? 0 : sum;
}

inline std::uint64_t multiply_mod(std::uint64_t a, std::uint64_t b) {
    unsigned __int128 product = static_cast<unsigned __int128>(a) * b;
    product = (product & modulus) + (product >> 61);
    std::uint64_t reduced = static_cast<std::uint64_t>(product);
    reduced = (reduced & modulus) + (reduced >> 61);
    return reduced == modulus ? 0 : reduced;
}

struct RowInfo {
    std::uint64_t offset = 0;
    std::uint32_t length = 0;
};

class Table {
  public:
    explicit Table(int n)
        : n_(n), side_(n + 1), rows_(side_ * side_ * side_) {
        std::uint64_t offset = 0;
        for (int weight = 1; weight <= n_; ++weight) {
            for (int ell = 1; ell <= weight; ++ell) {
                for (int a = 0; a <= weight - ell; ++a) {
                    const int q = weight - ell - a;
                    const int length = a == 0 ? q + 1 : a + q;
                    rows_[index(ell, a, q)] = {
                        offset, static_cast<std::uint32_t>(length)};
                    offset += length;
                }
            }
        }
        values_.assign(offset, 0);
    }

    const RowInfo& info(int ell, int a, int q) const {
        return rows_[index(ell, a, q)];
    }

    std::uint64_t* row(int ell, int a, int q) {
        return values_.data() + info(ell, a, q).offset;
    }

    const std::uint64_t* row(int ell, int a, int q) const {
        return values_.data() + info(ell, a, q).offset;
    }

    std::uint64_t entries() const { return values_.size(); }

  private:
    int n_;
    std::size_t side_;
    std::vector<RowInfo> rows_;
    std::vector<std::uint64_t> values_;

    std::size_t index(int ell, int a, int q) const {
        return (static_cast<std::size_t>(ell) * side_ + a) * side_ + q;
    }
};

int parse_n(const char* text) {
    char* end = nullptr;
    const long value = std::strtol(text, &end, 10);
    if (text == end || *end != '\0' || value < 0 || value > 200)
        throw std::invalid_argument("N must be between 0 and 200");
    return static_cast<int>(value);
}

}  // namespace

int main(int argc, char** argv) {
    try {
        if (argc != 2)
            throw std::invalid_argument("usage: av12453_dense_mod_verify N");
        const int n = parse_n(argv[1]);
        Table kernel(n);
        const auto started = std::chrono::steady_clock::now();
        std::uint64_t multiply_adds = 0;

        const auto add_row = [](std::uint64_t* target,
                                const std::uint64_t* source,
                                std::uint32_t length,
                                std::uint64_t scale = 1) {
            if (scale == 1) {
                for (std::uint32_t d = 0; d < length; ++d)
                    target[d] = add_mod(target[d], source[d]);
            } else {
                for (std::uint32_t d = 0; d < length; ++d)
                    target[d] = add_mod(
                        target[d], multiply_mod(scale, source[d]));
            }
        };

        for (int weight = 1; weight <= n; ++weight) {
            for (int ell = 1; ell <= weight; ++ell) {
                for (int a = 0; a <= weight - ell; ++a) {
                    const int q = weight - ell - a;
                    const RowInfo& output_info = kernel.info(ell, a, q);
                    std::uint64_t* output = kernel.row(ell, a, q);

                    for (int h = 0; h < a; ++h) {
                        const int source_q = a + q - h - 1;
                        const RowInfo& source = kernel.info(ell, h, source_q);
                        add_row(output, kernel.row(ell, h, source_q),
                                source.length);
                    }
                    for (int r = 0; r < q; ++r) {
                        const int source_ell = ell + q - r - 1;
                        const RowInfo& source = kernel.info(source_ell, a, r);
                        add_row(output, kernel.row(source_ell, a, r),
                                source.length);
                    }

                    if (ell == 1) {
                        if (a == 0) output[q] = add_mod(output[q], 1);
                    } else {
                        add_row(output, kernel.row(ell - 1, a, q),
                                output_info.length, 2);
                    }

                    for (int left_ell = 1; left_ell < ell - 1; ++left_ell) {
                        const int right_ell = ell - 1 - left_ell;
                        for (int left_drop = 0; left_drop <= a; ++left_drop) {
                            const int right_drop = a - left_drop;
                            const RowInfo& left_info =
                                kernel.info(left_ell, left_drop, q);
                            const std::uint64_t* left =
                                kernel.row(left_ell, left_drop, q);
                            for (std::uint32_t middle = 0;
                                 middle < left_info.length; ++middle) {
                                const RowInfo& right_info = kernel.info(
                                    right_ell, right_drop,
                                    static_cast<int>(middle));
                                add_row(output,
                                        kernel.row(right_ell, right_drop,
                                                   static_cast<int>(middle)),
                                        right_info.length, left[middle]);
                                multiply_adds += right_info.length;
                            }
                        }
                    }
                }
            }
        }

        const int side = n + 1;
        std::vector<std::uint64_t> empty(
            static_cast<std::size_t>(side) * side, 0);
        const auto empty_at = [&](int p, int q) -> std::uint64_t& {
            return empty[static_cast<std::size_t>(p) * side + q];
        };
        empty_at(0, 0) = 1;
        for (int mass = 1; mass <= n; ++mass) {
            for (int p = 0; p <= mass; ++p) {
                const int q = mass - p;
                std::uint64_t value = 0;
                for (int h = 0; h < p; ++h)
                    value = add_mod(value, empty_at(h, mass - h - 1));
                for (int r = 0; r < q; ++r) {
                    const int ell = q - r - 1;
                    if (ell == 0) {
                        value = add_mod(value, empty_at(p, r));
                        continue;
                    }
                    for (int c = 0; c <= p; ++c) {
                        const int drop = p - c;
                        const RowInfo& info = kernel.info(ell, drop, r);
                        const std::uint64_t* row = kernel.row(ell, drop, r);
                        for (std::uint32_t d = 0; d < info.length; ++d) {
                            value = add_mod(
                                value,
                                multiply_mod(row[d], empty_at(c, d)));
                            ++multiply_adds;
                        }
                    }
                }
                empty_at(p, q) = value;
            }
        }

        for (int degree = 0; degree <= n; ++degree)
            std::cout << degree << ' ' << empty_at(degree, 0) << '\n';
        const double seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - started).count();
        std::cerr << "# modulus=" << modulus
                  << " entries=" << kernel.entries()
                  << " madds=" << multiply_adds
                  << " seconds=" << seconds << '\n';
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "error: " << error.what() << '\n';
        return 2;
    }
}
