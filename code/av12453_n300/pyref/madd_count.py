"""Exact a-priori multiply-add count of the literal split evaluation in ref.py.

count(N) = sum over rows (l,a,q) with l>=3, l+a+q<=N of
           sum_{l1=1}^{l-2} sum_{a1=0}^{a} sum_{m<scount(a1,q)} scount(a-a1,m)
(the count actually executed differs only by the products skipped when a
first factor is zero, which happens only modulo P).
"""
def sc(a,q): return q+1 if a==0 else a+q
def S(M,a2):
    # sum_{m=0}^{M-1} sc(a2,m)
    if a2==0: return M*(M+1)//2
    return a2*M + M*(M-1)//2
def count(N):
    tot=0
    for a in range(0,N-2):
        for q in range(0,N-2-a):
            T=0
            for a1 in range(0,a+1):
                T+=S(sc(a1,q), a-a1)
            L=N-a-q
            if L>=3:
                tot+=T*((L-2)*(L-1)//2)
    return tot
if __name__=="__main__":
    import sys
    for N in [int(x) for x in sys.argv[1:]] or [10,20,40,60,80,100,150,200,300]:
        print(N, count(N))
