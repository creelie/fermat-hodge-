# Numerical check of the box relations used in sec14-reduction.md, section 1:
# (Add) R(t,a) - R(t',a) - R(t,a') + R(t',a') lies in S (all primitive characters
# of (Z/e')^x vanish on it), and (E3) the integral over a of (R - R^(3))(t, a) is
# constant in t modulo S.  Run on the configurations of an L_v_w_e file.
import sys, math, re, cmath
from fractions import Fraction as Fr
fn=sys.argv[1]
m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
N=2**v*3**w*e; T2=2**v; T3=3**w
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
Ue=[l for l in range(1,e) if math.gcd(l,e)==1]
# primitive characters of (Z/e)^x as value tables, via brute force on a generator set
def chars():
    # enumerate all characters by solving on cyclic decomposition: brute force via discrete logs
    # using the structure of (Z/e)^x: build characters as products over prime powers
    ps={}
    n=e;p=2
    while p*p<=n:
        while n%p==0: ps[p]=ps.get(p,0)+1; n//=p
        p+=1
    if n>1: ps[n]=ps.get(n,0)+1
    comps=[]
    for p,k in ps.items():
        q=p**k
        g=next(g for g in range(2,q) if math.gcd(g,q)==1 and all(pow(g,(p-1)*p**(k-1)//r,q)!=1 for r in set(f for f in range(2,p) if (p-1)%f==0 and all(f%d for d in range(2,f)))|({p} if k>1 else set())))
        phi=(p-1)*p**(k-1); lg={pow(g,i,q):i for i in range(phi)}
        comps.append((p,k,q,phi,lg))
    res=[]
    def rec(i,cur):
        if i==len(comps): res.append(cur); return
        p,k,q,phi,lg=comps[i]
        for j in range(phi):
            # primitive mod q iff not trivial on 1+q/p
            kq=[u for u in range(1,q) if math.gcd(u,q)==1 and (u-1)%(q//p)==0]
            if all(j*lg[u]%phi==0 for u in kq): continue
            rec(i+1,cur+[(q,phi,lg,j)])
    rec(0,[])
    return [ (lambda c: {l: cmath.exp(2j*cmath.pi*sum(jj*lg[l%q]/phi for (q,phi,lg,jj) in c)) for l in Ue})(c) for c in res]
CH=chars()
def inS(f):  # f: dict label->Fraction
    return all(abs(sum(complex(val)*ch[l] for l,val in f.items()))<1e-7 for ch in CH)
def add(f,l,c):
    f[l]=f.get(l,0)+c
def R(Bc, t, a):
    f={}
    for (j,i,tx,ax,lx) in Bc:
        in2 = (j<=1) or (t%2**j==tx)
        in3 = (i==0) or (a%3**i==ax)
        if in2 and in3: add(f,lx,1)
        in2n = (j<=1) or ((-t)%2**j==tx)
        in3n = (i==0) or ((-a)%3**i==ax)
        if in2n and in3n: add(f,(-lx)%e,-1)
    return f
def co(x):
    n=N//math.gcd(x,N); u=x//(N//n); j=vp(n,2); i=vp(n,3)
    return (j,i,u%2**j,u%3**i,u%e)
U2=[t for t in range(1,T2,2)] if v>=1 else [1]
U3=[a for a in range(1,T3) if a%3] if w>=1 else [1]
bad=0; tot=0
for line in open(fn):
    wds=line.split()
    if not wds or wds[0]!='C': continue
    B=[int(t.split('/')[0]) for t in wds[5:]]
    Bc=[co(x) for x in B]
    B3=[(j,i,(tx*pow(3,-1,2**j))%2**j if j>=1 else 0,ax,(lx*pow(3,-1,e))%e) for (j,i,tx,ax,lx) in Bc if i>=1]
    tot+=1; ok=True
    t0,a0=U2[0],U3[0]
    base=R(Bc,t0,a0)
    for t in U2:
        for a in U3:
            f={}
            for l,c in R(Bc,t,a).items(): add(f,l,c)
            for l,c in R(Bc,t0,a).items(): add(f,l,-c)
            for l,c in R(Bc,t,a0).items(): add(f,l,-c)
            for l,c in base.items(): add(f,l,c)
            if not inS(f): ok=False
    def E3(t):
        f={}
        for a in U3:
            for l,c in R(Bc,t,a).items(): add(f,l,Fr(c,len(U3)))
            for l,c in R(B3,t,a).items(): add(f,l,Fr(-c,len(U3)))
        return f
    e0=E3(t0)
    for t in U2:
        f=E3(t)
        for l,c in e0.items(): add(f,l,-c)
        if not inS(f): ok=False
    if not ok: bad+=1
print(fn,'configurations',tot,'violations',bad,'primitive chars',len(CH))
