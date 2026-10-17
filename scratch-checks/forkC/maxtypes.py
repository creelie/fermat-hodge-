# Tally the configurations of all L files by their set of maximal types
# (maximal for divisibility among the 2,3-parts of the orders), to check the
# reduction of sec14-composite.md, C4-C10: a configuration with a maximal
# type 4, 8 or 9, or with D' = 3, does not occur except at e' = 35 (types 4, 8
# have a chain but are filtered only by the fibre test, so they may occur).
import sys, glob, math, re
from collections import Counter
def part23(n):
    d=1
    for p in (2,3):
        while n%p==0: n//=p; d*=p
    return d
def lcm(a,b): return a*b//math.gcd(a,b)
tally=Counter(); ex=Counter()
for fn in sorted(glob.glob('/dev/shm/tmpb/forkC/data/L_*_*_*.txt')):
    m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt$', fn.split('/')[-1])
    if not m: continue
    v,w,e=map(int,m.groups())
    for line in open(fn):
        if not line.startswith('C'): continue
        els=[tuple(map(int,t.split('/'))) for t in line.split(':')[1].split()]
        ty=set(part23(o) for x,o in els)
        mx=frozenset(d for d in ty if not any(d2!=d and d2%d==0 for d2 in ty))
        Dp=1
        for d in ty: Dp=lcm(Dp,d)
        key=(tuple(sorted(mx)),Dp)
        tally[key]+=1
        if e not in (35,55): ex[(key,e)]+=1
for k in sorted(tally): print('maxtypes',k[0],'Dp',k[1],'count',tally[k])
print('-- composites other than 35, 55:')
agg=Counter()
for (k,e),c in ex.items(): agg[k]+=c
for k in sorted(agg): print('maxtypes',k[0],'Dp',k[1],'count',agg[k], 'e:',sorted(set(e for (kk,e) in ex if kk==k)))
