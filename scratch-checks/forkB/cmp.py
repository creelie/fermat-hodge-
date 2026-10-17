# Compare the configurations of prop (mod p) with those of locD at the same level N:
# canonical form = lex-min sorted tuple over the units of Z/N (as in locD).
# A locD configuration missing from prop must contain a proper sub-multiset in
# the prop list (prop finds the solutions with no proper sub-solution through
# the base, which include all minimal ones).
import sys, math
from itertools import combinations
N=int(sys.argv[1]); fprop=sys.argv[2]; floc=sys.argv[3]
U=[t for t in range(1,N) if math.gcd(t,N)==1]
def canon(xs): return min(tuple(sorted(x*t%N for x in xs)) for t in U)
def read(fn):
    out=[]
    for line in open(fn):
        w=line.split()
        if w and w[0]=='C': out.append([int(t.split('/')[0]) for t in w[5:]])
    return out
A=set(canon(b) for b in read(fprop)); B=set(canon(b) for b in read(floc))
print('prop',len(A),'locD',len(B),'prop-locD',len(A-B))
for b in sorted(A-B): print('  only prop',b)
bad=0
for b in sorted(B-A):
    ok=False
    for k in range(1,len(b)):
        for sub in combinations(b,k):
            if canon(sub) in A: ok=True; break
        if ok: break
    if not ok: bad+=1; print('  locD not decomposed',b)
print('locD-prop',len(B-A),'not decomposed',bad)
