# Sort the configurations of an L_v_w_e file whose top 2-level is J >= 4 into the
# cases of the hand proof of Theorem A (notes/sec14-reduction.md):
#   C    : a level-0 top x = -3y with y, y* in B (the C-chain);
#   LL+  : a non-flat orbit with an S+ element at every label of L (Line Lemma);
#   LL-  : the same with S- (i = 1; Line Lemma after the mirror);
#   A3D  : i >= 2, one label carrying {parent (+), two siblings (-)} ((d)-chain of R4);
#   N1, N3 : the two i = 1 mixed shapes ((N1)/(N3)-chains of R4);
#   LL0  : all orbits flat, the tops are level-0 tops of one orbit with Z_0 = +-1_L;
#   P1   : all orbits flat, 3 level-0 tops and a K3-pair in O_0, a level-0 top in O_{K-1};
#   UNEXPECTED : anything else (the hand proof says there is none).
# It also checks (T1) (sibling differences of Phi_O lie in S) and the two-value shape.
import sys, math, re, cmath
from collections import Counter, defaultdict
fn=sys.argv[1]; J0=int(sys.argv[2]) if len(sys.argv)>2 else 4
m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
N=2**v*3**w*e
def vp(n,p):
    k=0
    while n%p==0: n//=p; k+=1
    return k
def co(x):
    n=N//math.gcd(x,N); u=x//(N//n); j=vp(n,2); i=vp(n,3)
    return j,i,u%2**j,u%3**i,u%e
U=[a for a in range(1,e) if math.gcd(a,e)==1]
ps=[p for p in range(2,e+1) if e%p==0 and all(p%q for q in range(2,p))]
def gen(m):
    for g in range(2,m):
        if math.gcd(g,m)==1 and len({pow(g,k,m) for k in range(1,m)})==sum(1 for a in range(1,m) if math.gcd(a,m)==1): return g
chars=[]  # all primitive characters mod e as dicts
def allchars():
    # characters of (Z/e)^x via CRT over prime powers
    comps=[]
    for p in ps:
        pk=p**vp(e,p); g=gen(pk); ph=pk//p*(p-1)
        lg={pow(g,k,pk):k for k in range(ph)}
        comps.append((p,pk,ph,lg))
    def rec(idx,cur):
        if idx==len(comps): chars.append(cur); return
        p,pk,ph,lg=comps[idx]
        for r in range(ph):
            # primitive: nontrivial on 1+pk/p Z
            ok=any(r*lg[a]%ph for a in lg if (a-1)%(pk//p)==0 and a!=1)
            if not ok: continue
            rec(idx+1,cur+[(pk,ph,lg,r)])
    rec(0,[])
allchars()
def chi(c,a):
    z=1
    for pk,ph,lg,r in c: z*=cmath.exp(2j*math.pi*r*lg[a%pk]/ph)
    return z
def inS(f):
    return all(abs(sum(val*chi(c,a) for a,val in f.items()))<1e-6 for c in chars)
def kstar(J):
    for k in range(N):
        if math.gcd(k,N)==1 and k%2**J==(-(1+2**(J-1)))%2**J and k%3**max(w,1)==1 and k%e==e-1: return k
res=Counter(); bad=[]
for line in open(fn):
    wds=line.split()
    if not wds or wds[0]!='C': continue
    B=sorted(int(t.split('/')[0]) for t in wds[5:])
    cs=[co(x) for x in B]
    J=max(c[0] for c in cs)
    if J<J0: continue
    I=max(c[1] for c in cs)
    M2=2**J; eta=1+2**(J-1); K=2**(J-3)
    s=Counter(B); tops=[x for x,c in zip(B,cs) if c[0]==J]
    ks=kstar(J)
    Cflag=any(co(y)[1]==1 and (-3*y)%N in s and (ks*y)%N in s for y in tops)
    def orbit(t): return frozenset({t%M2,t*eta%M2,-t%M2,-t*eta%M2})
    def sign(tx,t):
        if tx==t%M2: return 1,1
        if tx==t*eta%M2: return -1,1
        if tx==(-t)%M2: return -1,-1
        if tx==(-t*eta)%M2: return 1,-1
        return None
    A3=[a for a in range(3**max(I,1)) if a%3]
    def Phi(t,a):
        f=defaultdict(int)
        for x in tops:
            j,i,tx,b,mu=co(x); sg=sign(tx,t)
            if sg is None: continue
            ep,sgm=sg
            if (a-sgm*b)%3**i==0: f[sgm*mu%e]+=ep
        return {k:val for k,val in f.items() if val}
    def elems(t):
        out=[]
        for x in tops:
            j,i,tx,b,mu=co(x); sg=sign(tx,t)
            if sg is None: continue
            out.append((sg[0],i,sg[1]*b%3**i if i else 0,sg[1]*mu%e,x))
        return out
    orbs={}
    for x in tops:
        o=orbit(co(x)[2]); orbs[o]=min(o)
    nonflat=[]
    for o,t in orbs.items():
        vals=[Phi(t,a) for a in A3]
        for a in range(len(A3)):
            d=Counter(vals[0]); d.subtract(vals[a]); d={k:val for k,val in d.items() if val}
            if not inS(d): bad.append(('T1fail',B))
        if any(vv!=vals[0] for vv in vals): nonflat.append((o,t,vals))
    cls=None
    if Cflag: cls='C'
    elif len(nonflat)>1: cls='UNEXPECTED(two nonflat)'
    elif nonflat:
        o,t,vals=nonflat[0]
        distinct=[]
        for vv in vals:
            if vv not in distinct: distinct.append(vv)
        if len(distinct)!=2: cls='UNEXPECTED(values)'
        else:
            d=Counter(distinct[1]); d.subtract(distinct[0]); d={k:val for k,val in d.items() if val}
            sgn=set(d.values())
            if len(sgn)!=1 or abs(list(sgn)[0])!=1: cls='UNEXPECTED(diff)'
            else:
                hi=distinct[1] if list(sgn)[0]==1 else distinct[0]
                L=set(d)
                Us=[a for a,vv in zip(A3,vals) if vv==hi]
                lev=None
                for i in range(1,max(I,1)+1):
                    r={a%3**i for a in Us}
                    if len(r)==1 and len([a for a in A3 if a%3**i==Us[0]%3**i])==len(Us): lev=i; bb=Us[0]%3**i; break
                if lev is None: cls='UNEXPECTED(U)'
                else:
                    E=elems(t)
                    byl=defaultdict(list)
                    for el in E: byl[el[3]].append(el)
                    def Sp(l): return any(el[0]==1 and el[1]==lev and el[2]==bb for el in byl[l])
                    def Sm(l): return lev==1 and any(el[0]==-1 and el[1]==1 and el[2]==(-bb)%3 for el in byl[l])
                    Lp=[l for l in L if Sp(l)]; Lm=[l for l in L if Sm(l)]
                    if len(Lp)==len(L): cls='LL+'
                    elif len(Lm)==len(L): cls='LL-'
                    elif lev>=2 and len(Lp)==len(L)-1:
                        l4=[l for l in L if not Sp(l)][0]; g=sorted((el[0],el[1],el[2]) for el in byl[l4])
                        par=[el for el in byl[l4] if el[0]==1 and el[1]==lev-1 and el[2]==bb%3**(lev-1)]
                        sib=[el for el in byl[l4] if el[0]==-1 and el[1]==lev and el[2]%3**(lev-1)==bb%3**(lev-1) and el[2]!=bb]
                        cls='A3D' if len(byl[l4])==3 and len(par)==1 and len(sib)==2 else 'UNEXPECTED(i>=2)'
                    elif lev==1 and len(Lp)+len(Lm)==len(L) and len(L)==4:
                        t3=t*pow(3,-1,M2)%M2
                        E3=elems(t3)
                        if len(Lm)==1 and len(Lp)==3:
                            ls=Lm[0]; g=byl[ls]
                            okB=len(g)==2 and any(el[1]==0 and el[0]==1 for el in g)
                            e6=[el for el in E3 if el[1]==0 and el[0]==-1 and el[3]==ls*pow(3,-1,e)%e]
                            cls='N1' if okB and e6 and len(B)==6 else 'UNEXPECTED(mixed1)'
                        elif len(Lp)==1 and len(Lm)==3:
                            ls=Lp[0]; g=byl[ls]
                            okA=len(g)==2 and any(el[1]==0 and el[0]==-1 for el in g)
                            e6=[el for el in E3 if el[1]==0 and el[0]==1 and el[3]==ls*pow(3,-1,e)%e]
                            cls='N3' if okA and e6 and len(B)==6 else 'UNEXPECTED(mixed3)'
                        else: cls='UNEXPECTED(mixed)'
                    else: cls='UNEXPECTED(other)'
    else:
        # all flat, no C
        lev1=[x for x in tops if co(x)[1]>=1]
        if not lev1 and len(orbs)==1:
            t=list(orbs.values())[0]; f=Phi(t,1)
            cls='LL0' if len(set(f.values()))==1 and abs(list(f.values())[0])==1 and len(f)==len(tops) else 'UNEXPECTED(flat0)'
        else:
            cls='UNEXPECTED(flat)'
            for o,t in orbs.items():
                E=elems(t); l0=[el for el in E if el[1]==0]; l1=[el for el in E if el[1]==1]
                if len(l0)==3 and len(l1)==2 and len(set(el[0] for el in l0+l1))==1 and len(B)==6:
                    t3=t*pow(3,-1,M2)%M2; E3=elems(t3)
                    if len(E3)==1 and E3[0][1]==0 and len(orbs)==2: cls='P1'
    res[cls]+=1
    if cls.startswith('UNEXPECTED'): bad.append((cls,B))
print(fn,'J>=%d'%J0,dict(res))
for b in bad[:10]: print('  ',b[0],' '.join('%d,%d:%d,%d,%d'%co(x) for x in b[1]))
