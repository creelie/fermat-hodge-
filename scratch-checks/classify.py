import sys, math
from collections import Counter
def primes(M):
    ps=[];n=M;p=2
    while p*p<=n:
        if n%p==0:
            ps.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1: ps.append(n)
    return ps
def order(y,M): return M//math.gcd(y,M)
def classify(A,M):
    tags=[]
    # split: union of two zero-sum triples
    for i in range(1,6):
        for j in range(i+1,6):
            if (A[0]+A[i]+A[j])%M==0: tags.append('split'); break
        if tags: break
    h=M//2
    if M%2==0:
        s=set(A)
        if any((a+h)%M in s for a in A): tags.append('Tpair')
    for l in primes(M):
        if l==2: continue
        d=M//l
        for x in set(A):
            fib=set((x+j*d)%M for j in range(l))
            k=len(fib & set(A))
            if 2*k>=l+1: tags.append('fib%d:%d'%(l,k)); break
    return tags
for fn in sys.argv[1:]:
    M=int(fn[1:-4]) if fn.startswith('t') else None
    cnt=Counter(); none=[]
    for line in open(fn):
        w=line.split()
        if w and w[0]=='R':
            A=list(map(int,w[1:7])); t=classify(A,M)
            key='split' if 'split' in t else ('T' if 'Tpair' in t else ('fib' if any(x.startswith('fib') for x in t) else 'none'))
            cnt[key]+=1
            if key=='none': none.append(A)
    print(M, dict(cnt), none[:4])
