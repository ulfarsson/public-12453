// Polynomial-time enumeration of Av(iota_r direct-sum 231), for fixed r.
//
// Compile with:
//   g++ -O3 -DNDEBUG -std=c++20 av_ir231_poly.cpp -o av_ir231_poly
// Run with:
//   ./av_ir231_poly R [N]
//
// The forbidden pattern is 1,2,...,r,r+2,r+3,r+1.  The finite control is
// an r-tuple of patience-sorting gap sizes.  Sparse protected-tail kernels
// eliminate the otherwise composition-valued stack.  For fixed r, a coarse
// bound is O(N^(3r+2)) exact-integer operations and O(N^(2r+1)) storage.

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

// A small dependency-free nonnegative big integer.  Blocks use base 10^9.
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

using Control = std::vector<int>;
using Entry = std::pair<int, Big>;
using Row = std::vector<Entry>;

struct ControlHash {
    std::size_t operator()(const Control& value) const noexcept {
        std::size_t seed = value.size();
        for (int coordinate : value) {
            seed ^= static_cast<std::size_t>(coordinate + 0x9e3779b9U)
                + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};

static void generate_weak_compositions(
    int remaining,
    int position,
    Control& current,
    std::vector<Control>& output) {
    if (position + 1 == static_cast<int>(current.size())) {
        current[position] = remaining;
        output.push_back(current);
        return;
    }
    for (int value = 0; value <= remaining; ++value) {
        current[position] = value;
        generate_weak_compositions(
            remaining - value, position + 1, current, output);
    }
}

static int parse_nonnegative(const char* text, const char* name) {
    try {
        std::size_t used = 0;
        const long long value = std::stoll(text, &used);
        if (text[used] != '\0' || value < 0 || value > 1000000)
            throw std::invalid_argument("range");
        return static_cast<int>(value);
    } catch (...) {
        std::cerr << "invalid " << name << ": " << text << '\n';
        std::exit(2);
    }
}

int main(int argc, char** argv) {
    if (argc < 2 || argc > 3) {
        std::cerr << "usage: " << argv[0] << " R [N]\n";
        return 2;
    }
    const int r = parse_nonnegative(argv[1], "R");
    const int max_n = argc == 3 ? parse_nonnegative(argv[2], "N") : 30;
    if (r < 1) {
        std::cerr << "R must be positive\n";
        return 2;
    }

    // Enumerate every r-dimensional control of weight at most N.  IDs are
    // assigned in increasing weight, which is also the topological order for
    // the empty-stack dynamic program.
    std::vector<Control> controls;
    std::vector<int> control_weight;
    std::vector<std::vector<int>> ids_by_weight(max_n + 1);
    std::unordered_map<Control, int, ControlHash> control_id;
    Control work(r, 0);
    for (int weight = 0; weight <= max_n; ++weight) {
        std::vector<Control> level;
        generate_weak_compositions(weight, 0, work, level);
        ids_by_weight[weight].reserve(level.size());
        for (Control& control : level) {
            const int id = static_cast<int>(controls.size());
            control_id.emplace(control, id);
            controls.push_back(std::move(control));
            control_weight.push_back(weight);
            ids_by_weight[weight].push_back(id);
        }
    }

    // kernel[source][ell] is a sparse row indexed by endpoint control IDs.
    // Only ell <= N-weight(source) is allocated.
    std::vector<std::vector<Row>> kernel(controls.size());
    for (std::size_t id = 0; id < controls.size(); ++id)
        kernel[id].resize(max_n - control_weight[id] + 1);

    std::vector<Big> accumulator(controls.size());
    std::vector<unsigned char> marked(controls.size(), 0);
    std::vector<int> touched;
    touched.reserve(controls.size());

    auto find_id = [&](const Control& control) -> int {
        const auto found = control_id.find(control);
        if (found == control_id.end())
            throw std::logic_error("missing control state");
        return found->second;
    };

    auto touch_add = [&](int endpoint, const Big& value) {
        if (value.zero()) return;
        if (!marked[endpoint]) {
            marked[endpoint] = 1;
            touched.push_back(endpoint);
        }
        accumulator[endpoint] += value;
    };

    auto add_row = [&](const Row& source) {
        for (const auto& [endpoint, value] : source)
            touch_add(endpoint, value);
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
    std::size_t kernel_rows = 0;
    std::size_t nonzero_entries = 0;

    // K_ell(p,-), in increasing rank sum(p)+ell.  Every referenced kernel
    // has rank exactly one less (or less in the composed second transfer).
    for (int rank = 1; rank <= max_n; ++rank) {
        for (int ell = 1; ell <= rank; ++ell) {
            const int weight = rank - ell;
            for (int source : ids_by_weight[weight]) {
                const Control& p = controls[source];
                touched.clear();

                for (int band = 0; band + 1 < r; ++band) {
                    const int old_size = p[band];
                    for (int h = 0; h < old_size; ++h) {
                        Control target = p;
                        target[band] = h;
                        target[band + 1] += old_size - 1 - h;
                        add_row(kernel[find_id(target)][ell]);
                    }
                }

                const int old_size = p.back();
                for (int h = 0; h < old_size; ++h) {
                    const int d = old_size - 1 - h;
                    Control target = p;
                    target.back() = h;
                    add_row(kernel[find_id(target)][ell + d]);
                }

                if (ell == 1) {
                    touch_add(source, Big(1));
                } else {
                    add_row_twice(kernel[source][ell - 1]);
                }

                for (int a = 1; a < ell - 1; ++a) {
                    const int b = ell - 1 - a;
                    for (const auto& [middle, multiplicity] :
                         kernel[source][a]) {
                        add_scaled_row(kernel[middle][b], multiplicity);
                    }
                }

                std::sort(touched.begin(), touched.end());
                Row& output = kernel[source][ell];
                output.reserve(touched.size());
                for (int endpoint : touched) {
                    if (!accumulator[endpoint].zero())
                        output.emplace_back(
                            endpoint, std::move(accumulator[endpoint]));
                    accumulator[endpoint] = Big();
                    marked[endpoint] = 0;
                }
                ++kernel_rows;
                nonzero_entries += output.size();
            }
        }
    }

    // Empty-stack values G[p], in increasing sum(p).
    std::vector<Big> empty(controls.size());
    empty[find_id(Control(r, 0))] = Big(1);
    for (int weight = 1; weight <= max_n; ++weight) {
        for (int source : ids_by_weight[weight]) {
            const Control& p = controls[source];
            Big value;

            for (int band = 0; band + 1 < r; ++band) {
                const int old_size = p[band];
                for (int h = 0; h < old_size; ++h) {
                    Control target = p;
                    target[band] = h;
                    target[band + 1] += old_size - 1 - h;
                    value += empty[find_id(target)];
                }
            }

            const int old_size = p.back();
            for (int h = 0; h < old_size; ++h) {
                const int d = old_size - 1 - h;
                Control target = p;
                target.back() = h;
                const int target_id = find_id(target);
                if (d == 0) {
                    value += empty[target_id];
                } else {
                    for (const auto& [endpoint, multiplicity] :
                         kernel[target_id][d])
                        value += multiplicity * empty[endpoint];
                }
            }
            empty[source] = std::move(value);
        }
    }

    std::cout << "# r=" << r << " pattern=";
    for (int value = 1; value <= r; ++value) {
        if (value > 1) std::cout << ',';
        std::cout << value;
    }
    std::cout << ',' << r + 2 << ',' << r + 3 << ',' << r + 1 << '\n';

    Control root(r, 0);
    for (int n = 0; n <= max_n; ++n) {
        root[0] = n;
        std::cout << n << ' ' << empty[find_id(root)] << '\n';
    }

    const auto finished = std::chrono::steady_clock::now();
    const double seconds =
        std::chrono::duration<double>(finished - started).count();
    std::cout << "# controls=" << controls.size()
              << " kernel_rows=" << kernel_rows
              << " nonzero_entries=" << nonzero_entries
              << " seconds=" << seconds << '\n';
}
