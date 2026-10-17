# Z/2-valued homomorphisms on R_110 vanishing on S_110, invariant under a subgroup H of units; value on A
from math import gcd
import itertools
M=110
A=[19,29,39,55,79,109]
units=[t for t in range(1,M) if gcd(t,M)==1]
def gens():
    out=[]
    for y in range(1,M): out.append([y,(-y)%M])
    for l in (5,11):
        for x in range(M):
            if (l*x)%M: out.append([(x+j*M//l)%M for j in range(l)]+[(-l*x)%M])
    for x in range(M):
        if (2*x)%M: out.append([x,(x+55)%M,(-2*x)%M,55])
    return out
G=gens()
def subgroup(gs):
    H={1}
    while True:
        new={(h*g)%M for h in H for g in gs}|H
        if new==H: return H
        H=new
def solve(H):
    # variables: orbits of H on Z/110 - {0}
    orb={};orbs=[]
    for y in range(1,M):
        if y in orb: continue
        o=sorted({(h*y)%M for h in H}); idx=len(orbs); orbs.append(o)
        for z in o: orb[z]=idx
    n=len(orbs)
    rows=[]
    for g in G:
        r=0
        for y in g: r^=1<<orb[y]
        rows.append(r)
    pivots={}
    for r in rows:
        x=r
        for c in sorted(pivots):
            if (x>>c)&1: x^=pivots[c]
        if x:
            c=(x&-x).bit_length()-1
            for k in list(pivots):
                if (pivots[k]>>c)&1: pivots[k]^=x
            pivots[c]=x
    free=[c for c in range(n) if c not in pivots]
    null=[]
    for fc in free:
        f=1<<fc
        for c,r in pivots.items():
            if (r>>fc)&1: f|=1<<c
        null.append(f)
    res=[]
    # search all combos (small)
    for k in range(1,1<<len(null)) if len(null)<=16 else []:
        f=0
        for i in range(len(null)):
            if (k>>i)&1: f^=null[i]
        val=sum((f>>orb[a])&1 for a in A)%2
        if val:
            supp=sorted(z for c in range(n) if (f>>c)&1 for z in orbs[c])
            res.append(supp)
    return n,len(null),res
for name,gs in [('all units',units),('squares',[t*t%M for t in units]),('+-1',[M-1]),('{1}',[1]),('fourth powers',[pow(t,4,M) for t in units]),('-1 and squares',[M-1]+[t*t%M for t in units])]:
    H=subgroup(gs)
    n,k,res=solve(H)
    res.sort(key=len)
    print(name,'|H|=',len(H),'orbits',n,'null dim',k,'with value 1:',len(res))
    for s in res[:3]: print('   ',len(s),s)
