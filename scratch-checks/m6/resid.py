# For residual files R_v_w_e.txt: for each residual configuration, the 2,3-part
# D' of the lcm of its orders, its size, and its canonical form after rescaling
# to level D' e'.
import sys, math, re
from collections import Counter, defaultdict
def part23(n):
    d=1
    for p in (2,3):
        while n%p==0: n//=p; d*=p
    return d
def lcm(a,b): return a*b//math.gcd(a,b)
for fn in sys.argv[1:]:
    m=re.match(r'R_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
    N=2**v*3**w*e
    stat=Counter(); forms=defaultdict(set)
    for line in open(fn):
        if not line.startswith('   '): continue
        els=[tuple(map(int,t.split('/'))) for t in line.split()]
        L=1
        for x,o in els: L=lcm(L,o)
        Dp=part23(L); Np=Dp*e; s=N//Np
        xs=[x//s for x,o in els]
        # canonical over units of Z/Np
        best=None
        for t in range(1,Np):
            if math.gcd(t,Np)!=1: continue
            b=tuple(sorted(x*t%Np for x in xs))
            if best is None or b<best: best=b
        stat[(Dp,len(els))]+=1; forms[Dp].add(best)
    print(fn, 'N=%d'%N, dict(sorted(stat.items())), {k:len(v) for k,v in sorted(forms.items())})
