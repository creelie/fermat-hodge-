# Print a shortest chain of standard moves for one sextuple at level M.
import sys, math
from fractions import Fraction
M = int(sys.argv[1]); A0 = sorted(int(t) % M for t in sys.argv[2].split(','))
DEPTH = int(sys.argv[3]) if len(sys.argv) > 3 else 4
CAP = 12
def primes(n):
    ps=[];p=2
    while p*p<=n:
        if n%p==0:
            ps.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1:ps.append(n)
    return ps
PR = primes(M)
def order(y): return M//math.gcd(y,M)
def depair(a):
    a=list(a); out=[]
    while a:
        x=a.pop()
        if (-x)%M in a: a.remove((-x)%M)
        else: out.append(x)
    return sorted(out)
def generates(a):
    g=M
    for x in a: g=math.gcd(g,x)
    return g==1
def split3(a):
    for i in range(1,6):
        for j in range(i+1,6):
            if (a[0]+a[i]+a[j])%M==0: return True
    return False
def prof(a): return sorted((order(x) for x in a), reverse=True)
P0 = prof(A0)
def success(b):
    if len(b)<=4: return 'small'
    if len(b)!=6: return None
    if not generates(b): return 'lowlevel'
    if split3(b): return 'split'
    if prof(b) < P0: return 'lower'
    return None
def sigs(y):
    out=[]
    for l in PR:
        d=M//l
        if l==2:
            if (2*y)%M and y!=M//2: out.append(('T',y,[y,(y+M//2)%M,(-2*y)%M,M//2]))
            for x in range(1,M):
                if (-2*x)%M==y and (2*x)%M: out.append(('T',x,[x,(x+M//2)%M,y,M//2])); break
        else:
            if (l*y)%M: out.append(('s%d'%l,y,[(y+j*d)%M for j in range(l)]+[(-l*y)%M]))
            for x in range(1,M):
                if (-l*x)%M==y and (l*x)%M: out.append(('s%d'%l,x,[(x+j*d)%M for j in range(l)]+[y])); break
    return out
def apply(b,sg):
    b=list(b); miss=[]
    for s in sg:
        if s in b: b.remove(s)
        else: miss.append(s)
    if len(miss)==len(sg): return None
    return depair(b+[(-s)%M for s in miss])
def search(b,depth,path):
    s=success(b)
    if s: return path+[(s,b)]
    if depth==0: return None
    seen=set()
    for y in sorted(set(b)):
        for name,x,sg in sigs(y):
            key=(name,x)
            if key in seen: continue
            seen.add(key)
            c=apply(b,sg)
            if c is None or len(c)>CAP: continue
            r=search(c,depth-1,path+[((name,x),c)])
            if r: return r
    return None
for d in range(1,DEPTH+1):
    r=search(A0,d,[('start',A0)])
    if r:
        for step,b in r: print(step, b)
        break
else: print('none')
