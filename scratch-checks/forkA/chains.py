# For configurations in an L_v_w_e file having an element whose 2-part >= 2^J0
# or 3-part >= 3^I0, print the shortest local chain found (depth <= DEPTH).
import sys, math, re
sys.setrecursionlimit(10000)
fn=sys.argv[1]; J0=int(sys.argv[2]); I0=int(sys.argv[3]); DEPTH=int(sys.argv[4]); LIM=int(sys.argv[5]) if len(sys.argv)>5 else 10**9
m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
N=2**v*3**w*e
import importlib.util
src=open('lchain.py').read().split('for fn in files:')[0]
src=src.replace("N = int(sys.argv[1]); DEPTH = int(sys.argv[2]); files = sys.argv[3:]","")
g={'N':N,'sys':sys}
exec(src,g)
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
cnt=0
for line in open(fn):
    wds=line.split()
    if not wds or wds[0]!='C': continue
    B=sorted(int(t.split('/')[0]) for t in wds[5:])
    ords=[N//math.gcd(x,N) for x in B]
    if not any(vp(o,2)>=J0 or vp(o,3)>=I0 for o in ords): continue
    cnt+=1
    if cnt>LIM: break
    r=None
    for d in range(1,DEPTH+1):
        r=g['search'](B,B,d,[])
        if r: break
    print(' '.join('%d/%d'%(x,o) for x,o in zip(B,ords)))
    if r:
        for name,x,c in r: print('    %s at %d/%d -> %s'%(name,x,N//math.gcd(x,N),' '.join('%d/%d'%(y,N//math.gcd(y,N)) for y in c)))
    else: print('    NO CHAIN')
