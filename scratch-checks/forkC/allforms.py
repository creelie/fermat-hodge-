# For configuration files L_v_w_e.txt: group the configurations by D' (the
# 2,3-part of the lcm of their orders), list the multiset of types (2,3-parts
# of the orders), the flags c, d of locG, and the canonical form at level D'e'.
import sys, math, re
from collections import defaultdict
def part23(n):
    d=1
    for p in (2,3):
        while n%p==0: n//=p; d*=p
    return d
def lcm(a,b): return a*b//math.gcd(a,b)
for fn in sys.argv[1:]:
    m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
    N=2**v*3**w*e
    out=defaultdict(set)
    for line in open(fn):
        if not line.startswith('C'): continue
        hd,_,body=line.partition(':')
        fl=re.findall(r'([cd])=(\d)',hd); fl=''.join(k for k,x in fl if x=='1') or '-'
        els=[tuple(map(int,t.split('/'))) for t in body.split()]
        L=1
        for x,o in els: L=lcm(L,o)
        Dp=part23(L); Np=Dp*e; s=N//Np
        xs=[x//s for x,o in els]
        best=None
        for t in range(1,Np):
            if math.gcd(t,Np)!=1: continue
            b=tuple(sorted(x*t%Np for x in xs))
            if best is None or b<best: best=b
        ty=tuple(sorted(part23(o) for x,o in els))
        out[Dp].add((ty,fl,best))
    print('==',fn,'N=%d'%N)
    for Dp in sorted(out):
        for ty,fl,b in sorted(out[Dp]):
            print('  D\'=%d types=%s flags=%s form=%s'%(Dp,','.join(map(str,ty)),fl,' '.join(map(str,b))))
