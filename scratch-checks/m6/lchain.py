# Local chains for e'-local configurations at level N = D e'.
# Input lines "C n= c= d= : x/ord ...".  A chain of standard moves sigma_{l,x}
# (l = 3 or l | e', fibre inside Z/N) and T(x) (v >= 1), using only elements of
# the current local multiset for S, is accepted when the final local multiset
# has at most |B| elements and the move is lowering: the largest order in the
# symmetric difference of order multisets lies on the removed side, or the
# final local multiset has at most |B| - 2 elements.
import sys, math
from collections import Counter
N = int(sys.argv[1]); DEPTH = int(sys.argv[2]); files = sys.argv[3:]
def primes(n):
    ps=[];p=2
    while p*p<=n:
        if n%p==0:
            ps.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1:ps.append(n)
    return ps
PR = [l for l in primes(N)]
def order(y): return N//math.gcd(y,N)
def depair(a):
    a=list(a); out=[]
    while a:
        x=a.pop()
        if (-x)%N in a: a.remove((-x)%N)
        else: out.append(x)
    return sorted(out)
def sigs(y):
    out=[]
    for l in PR:
        d=N//l
        if l==2:
            if (2*y)%N and y!=N//2: out.append(('T',y,[y,(y+N//2)%N,(-2*y)%N,N//2]))
            for x in range(1,N):
                if (-2*x)%N==y and (2*x)%N and x!=N//2: out.append(('T',x,[x,(x+N//2)%N,y,N//2]))
        else:
            if (l*y)%N: out.append(('s%d'%l,y,[(y+j*d)%N for j in range(l)]+[(-l*y)%N]))
            for x in range(1,N):
                if (-l*x)%N==y and (l*x)%N: out.append(('s%d'%l,x,[(x+j*d)%N for j in range(l)]+[y]))
    return out
def apply(b,sg):
    b=list(b); miss=[]; hit=0
    for s in sg:
        if s in b: b.remove(s); hit+=1
        else: miss.append(s)
    if hit==0: return None
    return depair(b+[(-s)%N for s in miss])
def ok(B, b):
    if len(b) <= len(B) - 2: return True
    if len(b) > len(B): return False
    R = Counter(order(x) for x in B); Dd = Counter(order(x) for x in b)
    rem = R - Dd; add = Dd - R
    if not rem: return False
    return max(rem) > (max(add) if add else 0)
def search(B, b, depth, path):
    if path and ok(B, b): return path
    if depth == 0: return None
    seen=set()
    for y in sorted(set(b)):
        for name,x,sg in sigs(y):
            if (name,x) in seen: continue
            seen.add((name,x))
            c=apply(b,sg)
            if c is None or len(c)>12: continue
            r=search(B,c,depth-1,path+[(name,x,c)])
            if r: return r
    return None
for fn in files:
    tot=0; bad=[]
    for line in open(fn):
        w=line.split()
        if not w or w[0]!='C': continue
        B=sorted(int(t.split('/')[0]) for t in w[5:])
        tot+=1
        r=None
        for d in range(1,DEPTH+1):
            r=search(B,B,d,[])
            if r: break
        if not r: bad.append(B)
    print(fn, 'total', tot, 'nochain', len(bad))
    for B in bad: print('  ', ' '.join('%d/%d'%(x,order(x)) for x in B))
