# Is the sextuple {19,29,39,55,79,109} at level 110 balanced, and is its class outside S_110?
from fractions import Fraction
from math import gcd
M=110
A=[19,29,39,55,79,109]
units=[t for t in range(1,M) if gcd(t,M)==1]
print('sum',sum(A)%M,'h values',sorted(set(sum((t*a)%M for a in A)//M for t in units)))
# generators of S_110
gens=[]
def vec(ms):
    v=[0]*M
    for y in ms: v[y%M]+=1
    assert v[0]==0
    return v[1:]
for y in range(1,M): gens.append(vec([y,-y]))
for l in (5,11):
    for x in range(M):
        if (l*x)%M: gens.append(vec([x+j*M//l for j in range(l)]+[-l*x]))
for x in range(M):
    if (2*x)%M: gens.append(vec([x,x+M//2,-2*x,M//2]))
# integer row reduction (Hermite) of gens
def hnf(rows):
    rows=[r[:] for r in rows]
    n=len(rows[0]); piv=[]; R=[]
    col=0
    basis=[]
    for c in range(n):
        # gather rows with nonzero at c among remaining
        while True:
            nz=[r for r in rows if r[c]!=0]
            if len(nz)<=1: break
            nz.sort(key=lambda r: abs(r[c]))
            p=nz[0]
            new=[]
            for r in rows:
                if r is p or r[c]==0: new.append(r); continue
                q=r[c]//p[c]
                new.append([a-q*b for a,b in zip(r,p)])
            rows=new
        nz=[r for r in rows if r[c]!=0]
        if nz:
            p=nz[0]
            if p[c]<0: p=[-a for a in p]
            basis.append((c,p))
            rows=[r for r in rows if r[c]==0]
    return basis
B=hnf(gens)
def reduce(v):
    v=v[:]
    for c,p in B:
        if v[c]%p[c]: return None, v
        q=v[c]//p[c]
        v=[a-q*b for a,b in zip(v,p)]
    return v, None
r,_=reduce(vec(A))
print('in S_110:', r is not None and all(x==0 for x in r))
r2,_=reduce([2*x for x in vec(A)])
print('2A in S_110:', r2 is not None and all(x==0 for x in r2))

# functionals mod 2 vanishing on S_110: solve f . g = 0 mod 2
import itertools
G=[[x%2 for x in g] for g in gens]
n=M-1
# nullspace of G (as matrix rows=gens) over GF(2): f with G f = 0
rows=[int(''.join(map(str,g[::-1])),2) for g in G]
# gaussian elimination
piv={}
for r in rows:
    for c in range(n):
        if not (r>>c)&1: continue
        if c in piv: r^=piv[c]
        else: piv[c]=r; break
    # loop ensures reduce
# proper reduction
basis=[]
pivots={}
for r in rows:
    x=r
    for c in sorted(pivots):
        if (x>>c)&1: x^=pivots[c]
    if x:
        c=(x & -x).bit_length()-1
        # eliminate c from existing
        for k in list(pivots):
            if (pivots[k]>>c)&1: pivots[k]^=x
        pivots[c]=x
rank=len(pivots)
free=[c for c in range(n) if c not in pivots]
print('rank mod 2',rank,'nullity',len(free))
# nullspace vectors
null=[]
for fc in free:
    f=1<<fc
    for c,r in pivots.items():
        if (r>>fc)&1: f|=1<<c
    null.append(f)
Av=vec(A)
for f in null:
    val=sum(Av[i] for i in range(n) if (f>>i)&1)%2
    supp=[i+1 for i in range(n) if (f>>i)&1]
    print(val, supp)
