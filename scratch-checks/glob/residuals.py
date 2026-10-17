# Collect the residual local configurations (no local chain) at a prime-to-6
# part e from all files R_v_w_e.txt, rescaled to their minimal level D' e and
# put in canonical form (lex-min over the units of Z/(D' e)).
# Output: residuals_<e>.txt with lines "D' n : x1 x2 ..." at level D' e.
import sys, math, re, glob, os
def part23(n):
    d=1
    for p in (2,3):
        while n%p==0: n//=p; d*=p
    return d
def lcm(a,b): return a*b//math.gcd(a,b)
SRC = sys.argv[1]
for e in map(int, sys.argv[2:]):
    forms=set()
    for fn in glob.glob(os.path.join(SRC, 'R_*_%d.txt' % e)):
        m=re.match(r'R_(\d+)_(\d+)_(\d+)\.txt', os.path.basename(fn)); v,w,ee=map(int,m.groups())
        if ee!=e: continue
        N=2**v*3**w*e
        for line in open(fn):
            if not line.startswith('   '): continue
            els=[tuple(map(int,t.split('/'))) for t in line.split()]
            L=1
            for x,o in els: L=lcm(L,o)
            Dp=part23(L); Np=Dp*e; s=N//Np
            xs=[x//s for x,o in els]
            best=min(tuple(sorted(x*t%Np for x in xs)) for t in range(1,Np) if math.gcd(t,Np)==1)
            forms.add((Dp,best))
    with open('residuals_%d.txt'%e,'w') as f:
        for Dp,b in sorted(forms, key=lambda z:(len(z[1]),z[0],z[1])):
            f.write('%d %d : %s\n'%(Dp,len(b),' '.join(map(str,b))))
    print(e, len(forms))
