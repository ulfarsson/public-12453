// avoid12453.hpp -- INDEPENDENT avoidance test for the pattern 12453.
//
// This file deliberately shares no code with the sampler's state machine.
// It is derived only from the "trigger lemma" restatement of containment:
//
//   pi contains 12453  <=>  there is a 2-trigger c of pi (a letter that has
//   some smaller letter before it) such that the letters occurring after c
//   and larger than c contain the pattern 231.
//
// Proof sketch (the pattern is 12453 = (1,2,4,5,3)): an occurrence
// pi_{i1..i5} has values v1 < v2 < v5 < v3 < v4.  Then v2 is a 2-trigger
// (v1 < v2 sits before it) and (v3,v4,v5) lie after v2, above v2, and form
// 231 (middle, largest, smallest).  Conversely such a configuration together
// with the smaller letter before c gives an occurrence of 12453.
//
// 231-containment of a word w is decided in O(|w|) time:
//   maintain the stack of right-to-left maxima of the processed prefix;
//   an element leaves the stack exactly when a larger element appears after
//   it, i.e. exactly when it can serve as the "2" of a 231; so w contains
//   231 iff some letter is smaller than the largest already-evicted letter.
//
// Total cost O(n^2) per permutation.  For n <= 12 use brute_contains_12453()
// (plain O(n^5) subsequence search) as a second, even more naive, opinion.

#ifndef AVOID12453_HPP
#define AVOID12453_HPP

#include <vector>
#include <cstddef>

namespace av {

// does the word w contain the pattern 231 (i<j<k with w[k] < w[i] < w[j])?
template <class T>
inline bool contains_231(const T *w, std::size_t m, std::vector<T> &stack) {
    stack.clear();
    T maxEvicted = T(-1);          // values are >= 1 in our use
    bool haveEvicted = false;
    for (std::size_t i = 0; i < m; ++i) {
        const T x = w[i];
        if (haveEvicted && maxEvicted > x) return true;      // x is the "1"
        while (!stack.empty() && stack.back() < x) {
            const T y = stack.back(); stack.pop_back();
            if (!haveEvicted || y > maxEvicted) { maxEvicted = y; haveEvicted = true; }
        }
        stack.push_back(x);
    }
    return false;
}

// scratch space, so the test allocates nothing in a hot loop
struct Scratch {
    std::vector<int> sub;
    std::vector<int> stack;
};

// pi is a permutation of 1..n given as pi[0..n-1]
inline bool contains_12453(const int *pi, int n, Scratch &sc) {
    if (n < 5) return false;
    // prefix minima: pi[i] is a 2-trigger iff min(pi[0..i-1]) < pi[i]
    int runmin = pi[0];
    sc.sub.resize((std::size_t)n);
    for (int i = 1; i < n; ++i) {
        const int c = pi[i];
        if (runmin < c) {                       // c is a 2-trigger
            std::size_t m = 0;
            for (int k = i + 1; k < n; ++k)
                if (pi[k] > c) sc.sub[m++] = pi[k];
            if (m >= 3 && contains_231(sc.sub.data(), m, sc.stack)) return true;
        } else {
            runmin = c;
        }
    }
    return false;
}

inline bool avoids_12453(const int *pi, int n, Scratch &sc) {
    return !contains_12453(pi, n, sc);
}

// completely naive O(n^5) search, for n <= 12 cross-checks
inline bool brute_contains_12453(const int *pi, int n) {
    for (int a = 0; a < n; ++a)
    for (int b = a + 1; b < n; ++b) {
        if (!(pi[a] < pi[b])) continue;
        for (int c = b + 1; c < n; ++c) {
            if (!(pi[c] > pi[b])) continue;
            for (int d = c + 1; d < n; ++d) {
                if (!(pi[d] > pi[c])) continue;
                for (int e = d + 1; e < n; ++e)
                    if (pi[e] > pi[b] && pi[e] < pi[c]) return true;   // 1,2,4,5,3
            }
        }
    }
    return false;
}

}  // namespace av
#endif
