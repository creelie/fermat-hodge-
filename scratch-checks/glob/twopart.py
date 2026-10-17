# Global step, two maximal prime-to-6 parts e1, e2 (primes).  A sextuple with
# no chain is B1 + B2 + L, B_i a residual local configuration at e_i, and at
# most one low element (a 2,3-element), so M = lcm(D1 e1, D2 e2, ord(a)).
# For every pair of residuals and every relative unit, find the balanced
# sextuples (no pair, generating, not split) and test them for a chain.
# usage: twopart.py e1 e2   (reads residuals_<e>.txt)
import sys, math
sys.setrecursionlimit(10000)
e1, e2 = int(sys.argv[1]), int(sys.argv[2])
def load(e):
    out=[]
    for line in open('residuals_%d.txt'%e):
        a,b=line.split(':'); D,n=map(int,a.split())
        out.append((D,[int(t) for t in b.split()]))
    return out
R1, R2 = load(e1), load(e2)
def lcm(a,b): return a*b//math.gcd(a,b)
def primes(n):
    ps=[];p=2
    while p*p<=n:
        if n%p==0:
            ps.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1:ps.append(n)
    return ps
class Level:
    def __init__(s,M):
        s.M=M; s.U=[t for t in range(1,M) if math.gcd(t,M)==1]; s.PR=primes(M)
    def order(s,y): return s.M//math.gcd(y,s.M)
def balanced_defect(L,A):
    M=L.M
    return [3*M-sum((u*x)%M for x in A) for u in L.U]
def nopair(L,A):
    M=L.M; c=list(A)
    for i in range(len(c)):
        for j in range(i+1,len(c)):
            if (c[i]+c[j])%M==0: return False
    return True
def generates(L,a):
    g=L.M
    for x in a: g=math.gcd(g,x)
    return g==1
def split3(L,a):
    M=L.M
    for i in range(1,6):
        for j in range(i+1,6):
            if (a[0]+a[i]+a[j])%M==0: return True
    return False
def canon(L,A):
    return min(tuple(sorted((u*x)%L.M for x in A)) for u in L.U)
# chain search (standard moves T(x), sigma_{l,x}), success as in lowmove.c
def depair(M,a):
    a=list(a); out=[]
    while a:
        x=a.pop()
        if (-x)%M in a: a.remove((-x)%M)
        else: out.append(x)
    return sorted(out)
def chain(L,A0,DEPTH=3,CAP=12):
    M=L.M
    P0=sorted((L.order(x) for x in A0),reverse=True)
    def success(b):
        if len(b)<=4: return True
        if len(b)!=6: return False
        if not generates(L,b) or split3(L,b): return True
        return sorted((L.order(x) for x in b),reverse=True) < P0
    def sigs(y):
        out=[]
        for l in L.PR:
            d=M//l
            if l==2:
                if (2*y)%M and y!=M//2: out.append(('T',y,[y,(y+M//2)%M,(-2*y)%M,M//2]))
                for x in range(1,M):
                    if (-2*x)%M==y and (2*x)%M and x!=M//2: out.append(('T',x,[x,(x+M//2)%M,y,M//2]))
            else:
                if (l*y)%M: out.append(('s%d'%l,y,[(y+j*d)%M for j in range(l)]+[(-l*y)%M]))
                for x in range(1,M):
                    if (-l*x)%M==y and (l*x)%M: out.append(('s%d'%l,x,[(x+j*d)%M for j in range(l)]+[y]))
        return out
    def apply(b,sg):
        b=list(b); miss=[]; hit=0
        for s_ in sg:
            if s_ in b: b.remove(s_); hit+=1
            else: miss.append(s_)
        if hit==0: return None
        return depair(M,b+[(-s_)%M for s_ in miss])
    def search(b,depth,path):
        if path and success(b): return path
        if depth==0: return None
        seen=set()
        for y in sorted(set(b)):
            for name,x,sg in sigs(y):
                if (name,x) in seen: continue
                seen.add((name,x))
                c=apply(b,sg)
                if c is None or len(c)>CAP: continue
                r=search(c,depth-1,path+[(name,x)])
                if r: return r
        return None
    for d in range(1,DEPTH+1):
        r=search(sorted(A0),d,[])
        if r: return r
    return None
levels={}
found={}
for D1,B1 in R1:
    for D2,B2 in R2:
        n=len(B1)+len(B2)
        if n>6 or n<5: continue
        Lam=lcm(D1,D2)
        Ms=[Lam*e1*e2]
        if n==5 and Lam%2==1: Ms.append(2*Lam*e1*e2)
        for M in Ms:
            if M%2: continue
            if M not in levels: levels[M]=Level(M)
            L=levels[M]
            s1=M//(D1*e1); s2=M//(D2*e2)
            A1=[(s1*x)%M for x in B1]
            for t in L.U:
                A2=[(s2*t*x)%M for x in B2]
                A=A1+A2
                d=balanced_defect(L,A)
                if n==6:
                    if any(d): continue
                else:
                    a=d[0]
                    if not (0<a<M): continue
                    if any(((u*a)%M)!=du for u,du in zip(L.U,d)): continue
                    # a must be a 2,3-element
                    o=L.order(a); oo=o
                    for p in (2,3):
                        while oo%p==0: oo//=p
                    if oo!=1: continue
                    A=A+[a]
                if not nopair(L,A) or not generates(L,A) or split3(L,A): continue
                c=canon(L,A)
                if (M,c) in found: continue
                found[(M,c)]=(D1,B1,D2,B2)
print('e1=%d e2=%d: %d balanced sextuples'%(e1,e2,len(found)))
bad=0
for (M,c),src in sorted(found.items()):
    r=chain(levels[M],list(c))
    if r is None:
        bad+=1; print('  NOCHAIN M=%d'%M, c, src)
    else:
        print('  chain M=%d'%M, c, r)
print('nochain',bad)
