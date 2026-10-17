# For each small residual B at core p (level D p), compute g_B(t) = h_B(t) - |B|/2
# and check it depends only on t mod D; print values on (Z/D)^x and whether
# g_B = -g_tau for a 2,3-element tau (B + {tau} balanced).
import math, sys
from fractions import Fraction as F
def load(e, path):
    out=[]
    for line in open(path+'/residuals_%d.txt'%e):
        a,b=line.split(':'); D,n=map(int,a.split())
        out.append((D,[int(t) for t in b.split()]))
    return out
path=sys.argv[1]
for p in (5,7,11,13):
    for D,B in load(p,path):
        if len(B)>4: continue
        N=D*p
        U=[t for t in range(1,N) if math.gcd(t,N)==1]
        g={}
        ok=True
        for t in U:
            v=F(sum((t*b)%N for b in B),N)-F(len(B),2)
            k=t%D
            if k in g and g[k]!=v: ok=False
            g[k]=v
        UD=sorted(g)
        # tau in Z/N of order dividing D (multiple of p)
        taus=[]
        for tau in range(0,N,p):
            if tau==0: continue
            if all(g[t%D]+F((t*tau)%N,N)-F(1,2)==0 for t in U): taus.append(tau)
        print(p,D,B,'depends on t mod D' if ok else 'NOT', {k:str(g[k]) for k in UD}, 'tau:',taus)
