# fchainc.py: fork B's fchain.py with inverses pow(., -1, P), so that P may be any
# modulus prime to 6 whose prime factors are >= 29 (sigma_q moves, q | P, then
# never give a multiset of size <= 12 other than the current one).
# Local chains (lchain.py semantics) for configurations given in CRT form, in
# the formal regime or modulo a prime p >= 29.  An element is (s mod D, u):
# u = (sg, a, b) for sg*2^a*3^b (formal), u = (0,0,0) for u = 0; or u in Z/p.
# Moves: T(x) (D even) and sigma_3(x) (3 | D), anchored as in lchain.py; for
# p >= 29 the moves sigma_p never give a multiset of size <= 12 other than the
# current one, so lchain.py with these moves only finds the same chains.
# Orders: d p for u != 0, d for u = 0 (d = D/gcd(s, D)); formally p > 72 and
# order keys compare as (u != 0, d).
# usage: fchain.py D p DEPTH files...   (p = 0: formal; files from prop)
import sys, math
from collections import Counter
D=int(sys.argv[1]); P=int(sys.argv[2]); DEPTH=int(sys.argv[3]); files=sys.argv[4:]
FORMAL = (P==0)
import os
VERB = os.environ.get('VERB')=='1'
ZERO = (0,0,0) if FORMAL else 0
def uneg(u):
    if FORMAL: return (-u[0],u[1],u[2])
    return (-u)%P
def umul(u,k):  # k in {-2,-3}
    if FORMAL:
        if u==ZERO: return ZERO
        return (-u[0], u[1]+(k==-2), u[2]+(k==-3))
    return (u*k)%P
def udiv(u,k):
    if FORMAL:
        if u==ZERO: return ZERO
        return (-u[0], u[1]-(k==-2), u[2]-(k==-3))
    return (u*pow(k%P,-1,P))%P
def neg(x): return ((-x[0])%D, uneg(x[1]))
def isz(x): return x[0]%D==0 and x[1]==ZERO
HALF = (D//2, ZERO)
def order(x):
    d = D//math.gcd(x[0],D)
    hp = x[1]!=ZERO
    if FORMAL: return (1 if hp else 0, d)
    return d*P if hp else d
BOT = (-1,0) if FORMAL else 0
def mul(x,k): return ((k*x[0])%D, umul(x[1],k))
def divs(y,k):
    return [(s, udiv(y[1],k)) for s in range(D) if (k*s-y[0])%D==0]
def sigs(y):
    out=[]
    if D%2==0:
        if not isz(mul(y,2)) and y!=HALF:
            out.append(('T',y,[y,((y[0]+D//2)%D,y[1]),mul(y,-2),HALF]))
        for x in divs(y,-2):
            if not isz(x) and not isz(mul(x,2)) and x!=HALF:
                out.append(('T',x,[x,((x[0]+D//2)%D,x[1]),y,HALF]))
    if D%3==0:
        if not isz(mul(y,3)):
            out.append(('s3',y,[((y[0]+j*D//3)%D,y[1]) for j in range(3)]+[mul(y,-3)]))
        for x in divs(y,-3):
            if not isz(x) and not isz(mul(x,3)):
                out.append(('s3',x,[((x[0]+j*D//3)%D,x[1]) for j in range(3)]+[y]))
    return out
def depair(a):
    a=list(a); out=[]
    while a:
        x=a.pop(); nx=neg(x)
        if nx in a: a.remove(nx)
        else: out.append(x)
    return sorted(out)
def apply(b,sg):
    b=list(b); miss=[]; hit=0
    for s in sg:
        if s in b: b.remove(s); hit+=1
        else: miss.append(s)
    if hit==0: return None
    return depair(b+[neg(s) for s in miss])
def ok(B,b):
    if len(b)<=len(B)-2: return True
    if len(b)>len(B): return False
    R=Counter(order(x) for x in B); Dd=Counter(order(x) for x in b)
    rem=R-Dd; add=Dd-R
    if not rem: return False
    return max(rem)>(max(add) if add else BOT)
def search(B,b,depth,path):
    if path and ok(B,b): return path
    if depth==0: return None
    seen=set()
    for y in sorted(set(b)):
        for name,x,sg in sigs(y):
            if (name,x) in seen: continue
            seen.add((name,x))
            c=apply(b,sg)
            if c is None or len(c)>12: continue
            r=search(B,c,depth-1,path+[(name,x,sg,c)])
            if r: return r
    return None
def parse(line):
    w=line.split()
    if w[0]=='F':
        return [ (int(t.split(',')[0]), tuple(map(int,t.split(',')[1:]))) for t in w[3:] ]
    if w[0]=='C':
        N=D*P
        return [ (int(t.split('/')[0])%D, int(t.split('/')[0])%P) for t in w[5:] ]
    return None
def fmt(x):
    if FORMAL: return '%d:%s'%(x[0],','.join(map(str,x[1])))
    return '%d'%((x[0]+D*(((x[1]-x[0])*pow(D,-1,P))%P))%(D*P))
for fn in files:
    tot=0; bad=[]; chains=[]
    for line in open(fn):
        B=parse(line) if line.strip() else None
        if not B: continue
        B=sorted(B); tot+=1; r=None
        for d in range(1,DEPTH+1):
            r=search(B,B,d,[])
            if r: break
        if not r: bad.append(B)
        else: chains.append((B,r))
    print(fn,'total',tot,'nochain',len(bad))
    for B in bad: print('   ',' '.join(fmt(x) for x in B))
    if os.environ.get('DUMP')=='1':
        for B,r in chains:
            E=set(B)
            for nm,x,sg,c in r: E|=set(sg)|set(c)|set(neg(z) for z in sg)
            print('  elems',' '.join(fmt(z) for z in sorted(E)))
    if VERB:
        for B,r in chains:
            print('  chain',' '.join(fmt(x) for x in B),'|',' ; '.join('%s(%s)->[%s]'%(nm,fmt(x),' '.join(fmt(z) for z in c)) for nm,x,sg,c in r))
