/* cblas.h -- MINIMAL STUB for testing the -DUSE_CBLAS code path of
 * av12453_gemm_split_v2.cpp.  This is NOT a BLAS: it declares exactly the
 * enums and the one entry point (cblas_dgemm) that the engine uses, so that
 * the -DUSE_CBLAS build can be compiled and its numerical output compared
 * with the hand-written micro-kernel build.  Link it against cblas_ref.c,
 * which is a naive triple loop (correctness reference only -- it is slow and
 * says nothing about the speed of a real BLAS).
 *
 * The signatures follow the reference CBLAS binding (Netlib / OpenBLAS /
 * Apple Accelerate), so an engine that compiles against this header also
 * compiles against those.
 */
#ifndef AV12453_CBLAS_STUB_H
#define AV12453_CBLAS_STUB_H

#ifdef __cplusplus
extern "C" {
#endif

typedef enum CBLAS_ORDER { CblasRowMajor = 101, CblasColMajor = 102 } CBLAS_ORDER;
typedef enum CBLAS_TRANSPOSE {
    CblasNoTrans = 111, CblasTrans = 112, CblasConjTrans = 113
} CBLAS_TRANSPOSE;

void cblas_dgemm(const CBLAS_ORDER Order,
                 const CBLAS_TRANSPOSE TransA, const CBLAS_TRANSPOSE TransB,
                 const int M, const int N, const int K,
                 const double alpha, const double *A, const int lda,
                 const double *B, const int ldb,
                 const double beta, double *C, const int ldc);

#ifdef __cplusplus
}
#endif
#endif /* AV12453_CBLAS_STUB_H */
