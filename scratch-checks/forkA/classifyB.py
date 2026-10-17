# Theorem B consistency check (R6 of sec14-reduction.md).  For every configuration
# with 3-level >= 3 (2-level <= 3), report the case of R6 and which of the chain
# configurations it contains:
#   Cp : a top x of 2-level >= 1 with -2x in B           (T(x), lemma B5)
#   LL : Line Lemma rows at a top of 2-level >= 2         (Case I, full S+-S-)
#   P  : pattern P of Case II (sigma_5 then T, lemma B6)
# Case I = some top has 2-level >= 2 (a non-flat orbit), Case II otherwise.
# Claim checked: Case I => Cp or LL;  Case II => Cp or P.
import sys, math, re
bad=0; tally={}
for fn in sys.argv[1:]:
    m=re.match(r'L_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
    N=2**v*3**w*e
    def vp(n,p):
        k=0
        while n%p==0: n//=p; k+=1
        return k
    def order(x): return N//math.gcd(x,N)
    def co(x):
        n=order(x); u=x//(N//n); return (vp(n,2),vp(n,3))
    qs=[q for q in (5,7) if e%q==0 and (e//q)%q!=0]
    for line in open(fn):
        wds=line.split()
        if not wds or wds[0]!='C': continue
        B=sorted(int(t.split('/')[0]) for t in wds[5:])
        s=set(B); I=max(co(x)[1] for x in B)
        if I<3: continue
        tops=[x for x in B if co(x)[1]==I]
        case='I' if any(co(x)[0]>=2 for x in tops) else 'II'
        Cp=any(co(x)[0]>=1 and (-2*x)%N in s for x in tops)
        LL=False; P=False
        for q in qs:
            for x in tops:
                n=order(x)
                C=[(x+a*(N//q))%N for a in range(q)]
                C=[y for y in C if order(y)==n]
                inB=[y for y in C if y in s]; out=[y for y in C if y not in s]
                if co(x)[0]>=2 and len(inB)==(q-1)//2 and all((-y+N//2)%N in s for y in out):
                    LL=True
                if q==5 and co(x)[0]==1 and len(inB)==2 and len(out)==2:
                    zs=[(2*y)%N for y in out]; ws=[(-y+N//2)%N for y in out]
                    if sorted(inB+zs+ws)==B: P=True
        lab=('Cp ' if Cp else '')+('LL ' if LL else '')+('P' if P else '')
        ok=(Cp or LL) if case=='I' else (Cp or P)
        if not ok: bad+=1
        key=(fn.split('/')[-1],case,lab.strip())
        tally[key]=tally.get(key,0)+1
for k in sorted(tally): print(k,tally[k])
print('configurations outside the cases of R6:',bad)
