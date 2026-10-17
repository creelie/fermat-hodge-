# Abstract check of the label analysis of Step 2: at one label, the tops of an orbit
# are (eps, sig, level k, beta mod 3^k); the contribution is eps * 1[a = sig*beta mod 3^k].
# Constraints: no two at the same level and signed box with opposite eps (pair/T-pair);
# no two distinct ones of the same type (eps, sig) at one level k >= 1 with
# beta = beta' mod 3^(k-1) (a 3-fibre move).  Lists the multisets of size <= 3 whose
# function is c + 1_U, U a box of level >= 1, that contain neither an S+ element
# (signed box U, eps = +) nor, when U has level 1, an S- element (signed box -U, eps = -);
# and the multisets of size <= 2 with constant function.
import itertools
IM=3; P=[a for a in range(3**IM) if a%3]
els=[]
for k in range(IM+1):
    for b in ([0] if k==0 else [x for x in range(3**k) if x%3]):
        for ep in (1,-1):
            for sg in (1,-1): els.append((ep,sg,k,b))
def box(el): ep,sg,k,b=el; return (k,(sg*b)%3**k if k else 0)
def okset(S):
    for x,y in itertools.combinations(S,2):
        if box(x)==box(y) and x[0]!=y[0]: return False
        if x!=y and x[0]==y[0] and x[1]==y[1] and x[2]==y[2]>=1 and (x[3]-y[3])%3**(x[2]-1)==0: return False
    return True
def h(S):
    return tuple(sum(el[0] for el in S if el[2]==0 or (a-el[1]*el[3])%3**el[2]==0) for a in P)
found={}
for m in (1,2,3):
    for S in itertools.combinations_with_replacement(range(len(els)),m):
        S=[els[i] for i in S]
        if not okset(S): continue
        f=h(S); vals=sorted(set(f))
        if m<=2 and len(vals)==1:
            key=('const',tuple(sorted((el[0],el[2]) for el in S)))
            found[key]=found.get(key,0)+1; continue
        if len(vals)!=2 or vals[1]!=vals[0]+1: continue
        Uset=[a for a,x in zip(P,f) if x==vals[1]]
        lev=None
        for k in range(1,IM+1):
            r={a%3**k for a in Uset}
            if len(r)==1 and len(Uset)==len([a for a in P if a%3**k==Uset[0]%3**k]): lev=k; ub=Uset[0]%3**k; break
        if lev is None: continue
        sp=any(el[0]==1 and box(el)==(lev,ub) for el in S)
        sm=lev==1 and any(el[0]==-1 and box(el)==(1,(-ub)%3) for el in S)
        if sp and sm: key=('BOTH',)
        elif sp: key=('S+',lev>=2,m)
        elif sm: key=('S-',m)
        else:
            desc=tuple(sorted((el[0],el[2],'U' if box(el)==(lev,ub) else ('par' if el[2]<lev and ub%3**el[2]==box(el)[1] else 'sib' if el[2]==lev and ub%3**(lev-1)==box(el)[1]%3**(lev-1) else 'other')) for el in S))
            key=('NEITHER',lev,vals[0],desc)
        found[key]=found.get(key,0)+1
for k in sorted(found,key=str): print(k,found[k])
