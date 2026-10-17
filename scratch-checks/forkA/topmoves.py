# For configurations with max 2-adic valuation J >= J0 (or 3-adic >= I0), test
# elementary moves at the top elements: (c) x and -2x in B, (d) x and 2x+N/2 in B,
# (e) x and N/2 in B, where x has the maximal 2-part (resp. a 3-analogue).
import sys, math, re
from collections import Counter
fn=sys.argv[1]; J0=int(sys.argv[2])
m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
N=2**v*3**w*e
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
st=Counter(); ex=[]
for line in open(fn):
    wds=line.split()
    if not wds or wds[0]!='C': continue
    B=sorted(int(t.split('/')[0]) for t in wds[5:])
    o={x:N//math.gcd(x,N) for x in B}
    J=max(vp(o[x],2) for x in B)
    if J<J0: continue
    tops=[x for x in B if vp(o[x],2)==J]
    s=set(B)
    c=any((-2*x)%N in s for x in tops)
    d=any((2*x+N//2)%N in s for x in tops)
    ee=(N//2) in s
    key=('c' if c else '')+('d' if d else '')+('e' if ee else '')
    st[key or 'none']+=1
    if not key: ex.append(B)
print(fn,'J>=%d'%J0,dict(st))
for B in ex[:10]: print('  ',' '.join('%d/%d'%(x,N//math.gcd(x,N)) for x in B))
