# Configurations with max 2-adic valuation >= J0 (or 3-adic >= I0) in normalised
# coordinates: x = (N/n) u, printed as j,i:t,a,l with t = u mod 2^j, a = u mod 3^i,
# l = u mod e'.  Flags: C = level-(J,0) top x and level-(J,1) tops y, y* with
# x = -3y and y* = -eta*kappa*y (the sigma_3 then T chain); c, d = top moves.
import sys, math, re
fn=sys.argv[1]; J0=int(sys.argv[2]); I0=int(sys.argv[3]) if len(sys.argv)>3 else 99
m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
N=2**v*3**w*e
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
def co(x):
    n=N//math.gcd(x,N); u=x//(N//n); j=vp(n,2); i=vp(n,3)
    return (j,i,u%2**j,u%3**i,u%e)
for line in open(fn):
    wds=line.split()
    if not wds or wds[0]!='C': continue
    B=sorted(int(t.split('/')[0]) for t in wds[5:])
    o=[N//math.gcd(x,N) for x in B]
    J=max(vp(a,2) for a in o); I=max(vp(a,3) for a in o)
    if J<J0 and I<I0: continue
    s=set(B); tops=[x for x in B if vp(N//math.gcd(x,N),2)==J]
    c=any((-2*x)%N in s for x in tops); d=any((2*x+N//2)%N in s for x in tops)
    C=False
    for y in tops:
        jj,ii,_,_,_=co(y)
        if ii!=1: continue
        n=N//math.gcd(y,N)
        # -eta*kappa: unit = -(1+2^{J-1}) mod 2^J, 1 mod 3, -1 mod e'
        for k in range(N):
            if math.gcd(k,N)==1 and k%2**J==(-(1+2**(J-1)))%2**J and k%3==1 and k%e==e-1: break
        if (-3*y)%N in s and (k*y)%N in s: C=True
    print('J=%d I=%d'%(J,I),'c' if c else '-','d' if d else '-','C' if C else '-',' | ',
          '  '.join('%d,%d:%d,%d,%d'%co(x) for x in B))
