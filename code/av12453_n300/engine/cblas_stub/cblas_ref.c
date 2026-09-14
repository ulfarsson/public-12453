/* cblas_ref.c -- naive reference cblas_dgemm in C, for the -DUSE_CBLAS
 * correctness test of av12453_gemm_split_v2.cpp.  Row-major, no transpose,
 * alpha = beta = 1.0: exactly the one call the engine makes,
 *
 *   cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans,
 *               MPb, nsPad, K, 1.0, Ap, K, Bp, nsPad, 1.0, C, nsPad);
 *
 * Anything else aborts loudly rather than silently computing the wrong thing.
 *
 * Exactness.  Every A and B entry is an integer in [0,P) and, by the
 * PRODLIMIT accounting in the engine, every C entry stays a non-negative
 * integer below 2^53 at all times.  Below 2^53 binary64 represents every
 * integer exactly and integer + and * are exact, so every partial sum here is
 * exact and the result does not depend on the summation order.  That is why
 * this loop reproduces the blocked micro-kernel bit for bit even though it
 * accumulates in a different order (and why a real BLAS would too).
 */
#include "cblas.h"
#include <stdio.h>
#include <stdlib.h>

void cblas_dgemm(const CBLAS_ORDER Order,
                 const CBLAS_TRANSPOSE TransA, const CBLAS_TRANSPOSE TransB,
                 const int M, const int N, const int K,
                 const double alpha, const double *A, const int lda,
                 const double *B, const int ldb,
                 const double beta, double *C, const int ldc)
{
    if (Order != CblasRowMajor || TransA != CblasNoTrans || TransB != CblasNoTrans) {
        fprintf(stderr, "cblas_ref: only (RowMajor, NoTrans, NoTrans) is implemented "
                        "(got order=%d transA=%d transB=%d)\n",
                (int)Order, (int)TransA, (int)TransB);
        abort();
    }
    if (alpha != 1.0 || beta != 1.0) {
        fprintf(stderr, "cblas_ref: only alpha = beta = 1.0 is implemented "
                        "(got alpha=%g beta=%g)\n", alpha, beta);
        abort();
    }
    if (M < 0 || N < 0 || K < 0 || lda < K || ldb < N || ldc < N) {
        fprintf(stderr, "cblas_ref: bad dimensions M=%d N=%d K=%d lda=%d ldb=%d ldc=%d\n",
                M, N, K, lda, ldb, ldc);
        abort();
    }
    /* i-k-j order: C[i][j] += A[i][k] * B[k][j], j innermost so the compiler
     * vectorizes it.  Exact for the reason given in the header comment. */
    for (int i = 0; i < M; ++i) {
        double *ci = C + (size_t)i * (size_t)ldc;
        const double *ai = A + (size_t)i * (size_t)lda;
        for (int k = 0; k < K; ++k) {
            const double a = ai[k];
            if (a == 0.0) continue;                    /* exact: adds 0.0 */
            const double *bk = B + (size_t)k * (size_t)ldb;
            for (int j = 0; j < N; ++j) ci[j] += a * bk[j];
        }
    }
}
