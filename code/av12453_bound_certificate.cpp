// Exact CRT-bound certificate for Av(12453).
//
// This small standalone program computes
//
//   B_N = sum_{m=0}^N binom(N,m)^2 |Av_m(1342)|,
//
// directly from Bona's algebraic generating function, then lists primes just
// below 2^62 until their product is greater than B_N.  Since deleting the
// left-to-right minima of a 12453-avoider gives a 1342-avoider, B_N is a
// rigorous upper bound for every requested coefficient through degree N.

#include <algorithm>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

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

    Big& multiply(const Big& other) {
        if (digits_.empty() || other.digits_.empty()) {
            digits_.clear();
            return *this;
        }
        const std::vector<std::uint32_t> left = digits_;
        std::vector<std::uint32_t> result(
            left.size() + other.digits_.size(), 0);
        for (std::size_t i = 0; i < left.size(); ++i) {
            unsigned __int128 carry = 0;
            for (std::size_t j = 0; j < other.digits_.size(); ++j) {
                const unsigned __int128 value =
                    static_cast<unsigned __int128>(left[i])
                        * other.digits_[j]
                    + result[i + j] + carry;
                result[i + j] =
                    static_cast<std::uint32_t>(value % base);
                carry = value / base;
            }
            std::size_t position = i + other.digits_.size();
            while (carry != 0) {
                if (position == result.size()) result.push_back(0);
                const unsigned __int128 value = result[position] + carry;
                result[position] =
                    static_cast<std::uint32_t>(value % base);
                carry = value / base;
                ++position;
            }
        }
        digits_ = std::move(result);
        trim();
        return *this;
    }

    Big& divide_exact(std::uint64_t divisor) {
        if (divisor == 0) throw std::invalid_argument("division by zero");
        unsigned __int128 remainder = 0;
        for (std::size_t position = digits_.size(); position-- > 0;) {
            const unsigned __int128 value = remainder * base
                                           + digits_[position];
            digits_[position] =
                static_cast<std::uint32_t>(value / divisor);
            remainder = value % divisor;
        }
        if (remainder != 0)
            throw std::logic_error("inexact Big division");
        trim();
        return *this;
    }

    Big& add(const Big& other) {
        if (digits_.size() < other.digits_.size())
            digits_.resize(other.digits_.size(), 0);
        std::uint64_t carry = 0;
        std::size_t position = 0;
        for (; position < other.digits_.size(); ++position) {
            const std::uint64_t value =
                static_cast<std::uint64_t>(digits_[position])
                + other.digits_[position] + carry;
            digits_[position] = static_cast<std::uint32_t>(value % base);
            carry = value / base;
        }
        while (carry != 0) {
            if (position == digits_.size()) digits_.push_back(0);
            const std::uint64_t value = digits_[position] + carry;
            digits_[position] = static_cast<std::uint32_t>(value % base);
            carry = value / base;
            ++position;
        }
        return *this;
    }

    // Subtract other, with the precondition *this >= other.
    Big& subtract(const Big& other) {
        if (*this < other) throw std::logic_error("negative Big subtraction");
        std::uint64_t borrow = 0;
        for (std::size_t position = 0;
             position < digits_.size(); ++position) {
            const std::uint64_t subtrahend =
                (position < other.digits_.size() ? other.digits_[position] : 0)
                + borrow;
            if (digits_[position] < subtrahend) {
                digits_[position] = static_cast<std::uint32_t>(
                    static_cast<std::uint64_t>(digits_[position]) + base
                    - subtrahend);
                borrow = 1;
            } else {
                digits_[position] = static_cast<std::uint32_t>(
                    digits_[position] - subtrahend);
                borrow = 0;
            }
        }
        if (borrow != 0) throw std::logic_error("Big subtraction underflow");
        trim();
        return *this;
    }

    friend bool operator<(const Big& left, const Big& right) {
        if (left.digits_.size() != right.digits_.size())
            return left.digits_.size() < right.digits_.size();
        for (std::size_t position = left.digits_.size(); position-- > 0;) {
            if (left.digits_[position] != right.digits_[position])
                return left.digits_[position] < right.digits_[position];
        }
        return false;
    }

    friend bool operator<=(const Big& left, const Big& right) {
        return !(right < left);
    }

    friend std::ostream& operator<<(std::ostream& out, const Big& value) {
        if (value.digits_.empty()) return out << '0';
        out << value.digits_.back();
        for (std::size_t position = value.digits_.size() - 1;
             position-- > 0;) {
            std::uint32_t block = value.digits_[position];
            std::uint32_t place = 100000000U;
            while (place != 0) {
                out << static_cast<char>('0' + block / place);
                block %= place;
                place /= 10;
            }
        }
        return out;
    }

  private:
    std::vector<std::uint32_t> digits_;

    void trim() {
        while (!digits_.empty() && digits_.back() == 0) digits_.pop_back();
    }
};

std::vector<Big> av1342_counts(int n) {
    std::vector<Big> b(static_cast<std::size_t>(n) + 1);
    if (n >= 0) b[0] = 1;
    if (n >= 1) b[1] = 1;
    if (n >= 2) b[2] = 2;

    // s_k=[x^k](1-8x)^(3/2).  Here s_2=24, and for k>=3,
    // s_k = 4(2k-5)s_{k-1}/k.  These s_k are positive integers.
    Big s = 24;
    for (int k = 3; k <= n; ++k) {
        s.multiply(static_cast<std::uint64_t>(4 * (2 * k - 5)));
        s.divide_exact(static_cast<std::uint64_t>(k));

        // For k>=3, comparison of coefficients in
        // 2(1+x)^3 B(x)=(1-8x)^(3/2)+1+20x-8x^2 gives this recurrence.
        Big current = s;
        current.divide_exact(2);
        Big correction = b[k - 1];
        correction.multiply(3);
        current.subtract(correction);
        correction = b[k - 2];
        correction.multiply(3);
        current.subtract(correction);
        current.subtract(b[k - 3]);
        b[k] = std::move(current);
    }
    return b;
}

Big av12453_bound(int n) {
    const std::vector<Big> b = av1342_counts(n);
    Big bound = 0;
    Big choose = 1;
    for (int m = 0; m <= n; ++m) {
        Big term = choose;
        term.multiply(choose);
        term.multiply(b[m]);
        bound.add(term);
        if (m != n) {
            choose.multiply(static_cast<std::uint64_t>(n - m));
            choose.divide_exact(static_cast<std::uint64_t>(m + 1));
        }
    }
    return bound;
}

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

int parse_n(const char* text) {
    std::size_t used = 0;
    const int n = std::stoi(text, &used);
    if (text[used] != '\0' || n < 0 || n > 1000)
        throw std::invalid_argument("N must lie in [0,1000]");
    return n;
}

}  // namespace

int main(int argc, char** argv) {
    try {
        const int n = argc == 2 ? parse_n(argv[1]) : 150;
        const Big bound = av12453_bound(n);
        Big product = 1;
        std::vector<std::uint64_t> primes;
        std::uint64_t candidate = (1ULL << 62) - 1;
        while (product <= bound) {
            while (!is_prime(candidate)) candidate -= 2;
            primes.push_back(candidate);
            product.multiply(candidate);
            candidate -= 2;
        }
        std::cout << "N=" << n << '\n';
        std::cout << "B_N=" << bound << '\n';
        std::cout << "prime_product=" << product << '\n';
        std::cout << "prime_count=" << primes.size() << '\n';
        for (std::uint64_t prime : primes) std::cout << prime << '\n';
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "error: " << error.what() << '\n';
        return 2;
    }
}
