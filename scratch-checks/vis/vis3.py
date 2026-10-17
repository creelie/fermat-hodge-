import sys, math
from vis import search
p=int(sys.argv[1]); M=6*p; lim=int(sys.argv[2]) if len(sys.argv)>2 else 20
nu=lambda A: sum(1 for a in A if math.gcd(a,M)==M//p)%2==1
def haspair(A): return any((M-a)%M in A for a in A) 
def split(A):
    from itertools import combinations
    idx=range(6)
    for c in combinations(idx,3):
        if 0 in c:
            if sum(A[i] for i in c)%M==0: return True
    return False
f=search(M,nu,4,5); print(M,'size4',f)
f=search(M,nu,6,lim)
print(M,'size6 count',len(f))
for A in f: print(A,'pair' if haspair(A) else '', 'split' if split(A) else '')
