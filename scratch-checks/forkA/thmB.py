# Theorem B data: for every configuration with 3-level >= I0 (default 3), list the
# tops (3-level I) with orbit k (base 2^k mod 3^I), position r (beta = sig*2^k*kappa^r),
# sign sig, 2-level j, signed 2-box c = sig*t mod 2^j, label lam = sig*mu mod e'.
# Also: flag Cp (x and -2x in B, x a top of 2-level >= 1), T1' flatness per orbit,
# and the values G_k(r) (with weights 1/phi(2^j)) as dicts label->coefficient.
import sys, math, re
from fractions import Fraction as Fr
fn=sys.argv[1]; I0=int(sys.argv[2]) if len(sys.argv)>2 else 3
m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
N=2**v*3**w*e
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
def co(x):
    n=N//math.gcd(x,N); u=x//(N//n); j=vp(n,2); i=vp(n,3)
    return (j,i,u%2**j,u%3**i,u%e)
def phi2(j): return 1 if j==0 else 2**(j-1)
for line in open(fn):
    wds=line.split()
    if not wds or wds[0]!='C': continue
    B=sorted(int(t.split('/')[0]) for t in wds[5:])
    cs=[co(x) for x in B]
    I=max(c[1] for c in cs)
    if I<I0: continue
    J=max(c[0] for c in cs)
    M3=3**I; kap=1+3**(I-1); K=3**(I-2)
    tops=[]
    for x,(j,i,t,b,mu) in zip(B,cs):
        if i!=I: continue
        found=None
        for k in range(K):
            for r in range(3):
                for sg in (1,-1):
                    if (sg*pow(2,k,M3)*pow(kap,r,M3))%M3==b: found=(k,r,sg)
        k,r,sg=found
        c=(sg*t)%(2**j) if j>0 else 0
        tops.append(dict(x=x,k=k,r=r,s=sg,j=j,c=c,lam=(sg*mu)%e))
    s=set(B)
    Cp=any((-2*x)%N in s and co(x)[0]>=1 and co(x)[1]==I for x in B)
    nontop=[ '%d,%d:%d,%d,%d'%c for c in cs if c[1]!=I]
    print('J=%d I=%d K=%d'%(J,I,K),'Cp' if Cp else '--',' nontops:',nontop)
    for tp in sorted(tops,key=lambda d:(d['k'],d['lam'],d['r'])):
        print('   k=%d r=%d s=%+d j=%d c=%d lam=%d'%(tp['k'],tp['r'],tp['s'],tp['j'],tp['c'],tp['lam']))
    # G_k(r)
    for k in range(K):
        G=[{} for _ in range(3)]
        for tp in tops:
            if tp['k']==k:
                d=G[tp['r']]; d[tp['lam']]=d.get(tp['lam'],0)+Fr(tp['s'],phi2(tp['j']))
            kk=(k+1)%K
            if tp['j']>=1 and tp['k']==kk:
                # tops of O_{k+1}; twist if k+1==K: sign -, label -, position r+1 (2^K=-kappa^2)
                r=tp['r']; sg=1; lam=tp['lam']
                if k+1==K: r=(r+1)%3; sg=-1; lam=(-lam)%e
                lab=(lam*pow(2,-1,e))%e
                d=G[r]; d[lab]=d.get(lab,0)-sg*Fr(tp['s'],phi2(tp['j']))
        if any(any(vv!=0 for vv in g.values()) for g in G):
            print('   G_%d:'%k,' | '.join(' '.join('%s:%s'%(l,c) for l,c in sorted(g.items()) if c!=0) for g in G))
