# Re-search the local chains of chains.py at the level L_B e' instead of N = D e':
# D_B = 2,3-part of the lcm of the orders in B, L_B = lcm(D_B, 6), and B is mapped
# into Z/(L_B e') by x -> x / (N / (L_B e')).  Only configurations with 2-part >= 2^J0
# or 3-part >= 3^I0 are treated.  Prints one summary line per file:
#   file  total  found_at_LB  nochain_at_LB  (and lists the configurations without one)
# usage: python3 chainsLB.py out/L_v_w_e.txt J0 I0 DEPTH
import sys, math, re
sys.setrecursionlimit(10000)
fn=sys.argv[1]; J0=int(sys.argv[2]); I0=int(sys.argv[3]); DEPTH=int(sys.argv[4])
m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
N=2**v*3**w*e
src=open('lchain.py').read().split('for fn in files:')[0]
src=src.replace("N = int(sys.argv[1]); DEPTH = int(sys.argv[2]); files = sys.argv[3:]","")
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
cache={}
def namespace(Np):
    if Np not in cache:
        g={'N':Np,'sys':sys}; exec(src,g); cache[Np]=g
    return cache[Np]
tot=0; bad=[]; seen=0
for line in open(fn):
    wds=line.split()
    if not wds or wds[0]!='C': continue
    B=sorted(int(t.split('/')[0]) for t in wds[5:])
    ords=[N//math.gcd(x,N) for x in B]
    if not any(vp(o,2)>=J0 or vp(o,3)>=I0 for o in ords): continue
    tot+=1
    L=1
    for o in ords: L=L*o//math.gcd(L,o)
    DB=2**vp(L,2)*3**vp(L,3); LB=DB*6//math.gcd(DB,6); Np=LB*e
    assert N%Np==0
    Bp=sorted((x//(N//Np))%Np for x in B)
    g=namespace(Np)
    r=None
    for d in range(1,DEPTH+1):
        r=g['search'](Bp,Bp,d,[])
        if r: break
    if not r: bad.append((Np,Bp))
print(fn,'total',tot,'nochain_at_LB',len(bad))
for Np,Bp in bad: print('  level',Np,' '.join('%d/%d'%(x,Np//math.gcd(x,Np)) for x in Bp))
