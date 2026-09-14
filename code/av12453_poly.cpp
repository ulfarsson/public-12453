// Faster C++ implementation of the transfer-kernel recurrence described in
// av12453_polytime.tex.  Compile with:
//   g++ -O3 -std=c++20 av12453_poly.cpp -o av12453_poly

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <utility>
#include <vector>

// A tiny nonnegative big integer is enough here and keeps this verifier
// dependency-free.  Coefficients are stored in base 10^9.
class Big {
  public:
    static constexpr std::uint32_t base = 1000000000U;
    std::vector<std::uint32_t> digits;

    Big(std::uint64_t value = 0) {
        while (value) {
            digits.push_back(static_cast<std::uint32_t>(value % base));
            value /= base;
        }
    }

    bool zero() const { return digits.empty(); }

    Big& operator+=(const Big& other) {
        const std::size_t size = std::max(digits.size(), other.digits.size());
        digits.resize(size, 0);
        std::uint64_t carry = 0;
        for (std::size_t p = 0; p < size; ++p) {
            const std::uint64_t sum = static_cast<std::uint64_t>(digits[p])
                + (p < other.digits.size() ? other.digits[p] : 0) + carry;
            digits[p] = static_cast<std::uint32_t>(sum % base);
            carry = sum / base;
        }
        if (carry) digits.push_back(static_cast<std::uint32_t>(carry));
        return *this;
    }

    friend Big operator+(Big left, const Big& right) {
        left += right;
        return left;
    }

    friend Big operator*(const Big& left, const Big& right) {
        if (left.zero() || right.zero()) return Big();
        Big product;
        product.digits.assign(left.digits.size() + right.digits.size(), 0);
        for (std::size_t a = 0; a < left.digits.size(); ++a) {
            std::uint64_t carry = 0;
            for (std::size_t b = 0; b < right.digits.size(); ++b) {
                const std::size_t p = a + b;
                const std::uint64_t value =
                    static_cast<std::uint64_t>(left.digits[a]) * right.digits[b]
                    + product.digits[p] + carry;
                product.digits[p] = static_cast<std::uint32_t>(value % base);
                carry = value / base;
            }
            std::size_t p = a + right.digits.size();
            while (carry) {
                if (p == product.digits.size()) product.digits.push_back(0);
                const std::uint64_t value = product.digits[p] + carry;
                product.digits[p] = static_cast<std::uint32_t>(value % base);
                carry = value / base;
                ++p;
            }
        }
        while (!product.digits.empty() && product.digits.back() == 0)
            product.digits.pop_back();
        return product;
    }

    friend bool operator==(const Big& value, int small) {
        return small == 0 && value.zero();
    }

    friend std::ostream& operator<<(std::ostream& out, const Big& value) {
        if (value.zero()) return out << '0';
        out << value.digits.back();
        for (std::size_t p = value.digits.size() - 1; p-- > 0;) {
            const std::uint32_t block = value.digits[p];
            std::uint32_t divisor = 100000000U;
            while (divisor > block && divisor > 1) {
                out << '0';
                divisor /= 10;
            }
            out << block;
        }
        return out;
    }
};
using Entry = std::pair<int, Big>;
using Row = std::vector<Entry>;

static int control_id(int i, int j) {
    return (j - 1) * (j - 2) / 2 + (i - 1);
}

int main(int argc, char** argv) {
    const int max_n = argc > 1 ? std::atoi(argv[1]) : 30;
    if (max_n < 0) return 2;
    const int limit = max_n + 2;
    const int controls = limit * (limit - 1) / 2;

    std::vector<int> id_i(controls), id_j(controls);
    for (int j = 2; j <= limit; ++j) {
        for (int i = 1; i < j; ++i) {
            const int id = control_id(i, j);
            id_i[id] = i;
            id_j[id] = j;
        }
    }

    // kernel[i][j][ell] is a sparse row indexed by endpoint control IDs.
    std::vector<std::vector<std::vector<Row>>> kernel(
        limit + 1,
        std::vector<std::vector<Row>>(
            limit + 1, std::vector<Row>(limit + 1)));

    std::vector<Big> accumulator(controls);
    std::vector<unsigned char> marked(controls, 0);
    std::vector<int> touched;
    touched.reserve(controls);

    auto touch_add = [&](int endpoint, const Big& value) {
        if (value == 0) return;
        if (!marked[endpoint]) {
            marked[endpoint] = 1;
            touched.push_back(endpoint);
        }
        accumulator[endpoint] += value;
    };

    auto add_row = [&](const Row& source) {
        for (const auto& [endpoint, value] : source) touch_add(endpoint, value);
    };

    auto add_row_twice = [&](const Row& source) {
        for (const auto& [endpoint, value] : source)
            touch_add(endpoint, value + value);
    };

    auto add_scaled_row = [&](const Row& source, const Big& scale) {
        for (const auto& [endpoint, value] : source)
            touch_add(endpoint, scale * value);
    };

    const auto started = std::chrono::steady_clock::now();
    std::size_t nonzero_entries = 0;
    std::size_t kernel_rows = 0;

    for (int rank = 3; rank <= limit; ++rank) {
        for (int j = 2; j < rank; ++j) {
            const int ell = rank - j;
            for (int i = 1; i < j; ++i) {
                touched.clear();

                for (int k = 1; k < i; ++k)
                    add_row(kernel[k][j - 1][ell]);

                for (int k = i + 1; k < j; ++k) {
                    const int delta = j - k - 1;
                    add_row(kernel[i][k][ell + delta]);
                }

                if (ell == 1) {
                    touch_add(control_id(i, j), Big(1));
                } else {
                    add_row_twice(kernel[i][j][ell - 1]);
                }

                for (int a = 1; a < ell - 1; ++a) {
                    const int b = ell - 1 - a;
                    for (const auto& [middle, multiplicity] :
                         kernel[i][j][a]) {
                        add_scaled_row(
                            kernel[id_i[middle]][id_j[middle]][b],
                            multiplicity);
                    }
                }

                std::sort(touched.begin(), touched.end());
                Row& output = kernel[i][j][ell];
                output.reserve(touched.size());
                for (int endpoint : touched) {
                    if (accumulator[endpoint] != 0)
                        output.emplace_back(endpoint,
                                            std::move(accumulator[endpoint]));
                    accumulator[endpoint] = 0;
                    marked[endpoint] = 0;
                }
                ++kernel_rows;
                nonzero_entries += output.size();
            }
        }
    }

    std::vector<Big> empty(controls);
    for (int j = 2; j <= limit; ++j) {
        for (int i = 1; i < j; ++i) {
            const int source = control_id(i, j);
            if (i == 1 && j == 2) {
                empty[source] = 1;
                continue;
            }
            Big value = 0;
            for (int k = 1; k < i; ++k)
                value += empty[control_id(k, j - 1)];
            for (int k = i + 1; k < j; ++k) {
                const int delta = j - k - 1;
                if (delta == 0) {
                    value += empty[control_id(i, k)];
                } else {
                    for (const auto& [endpoint, multiplicity] :
                         kernel[i][k][delta])
                        value += multiplicity * empty[endpoint];
                }
            }
            empty[source] = std::move(value);
        }
    }

    for (int n = 0; n <= max_n; ++n)
        std::cout << n << ' ' << empty[control_id(n + 1, n + 2)] << '\n';

    const auto finished = std::chrono::steady_clock::now();
    const double seconds =
        std::chrono::duration<double>(finished - started).count();
    std::cout << "# kernel_rows=" << kernel_rows
              << " nonzero_entries=" << nonzero_entries
              << " seconds=" << seconds << '\n';
}
