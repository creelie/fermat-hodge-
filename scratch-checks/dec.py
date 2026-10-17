import sys, itertools, math
def bal(B,M):
    h=None
    for t in range(1,M):
        if math.gcd(t,M)!=1: continue
        s=sum((t*b)%M for b in B)
        if h is None: h=s
        elif s!=h: return False
    return True
res={330:[[5,40,66,250,310,319]],390:[[5,78,130,275,305,377],[5,13,260,275,305,312]],110:[[1,24,62,71,81,91]],70:[[1,20,24,42,61,62]]}
for M,L in res.items():
    for A in L:
        ok=[]
        for tr in itertools.combinations(range(6),3):
            if 0 not in tr: continue
            a=[A[i] for i in tr]; b=[A[i] for i in range(6) if i not in tr]
            t=sum(a)%M
            if t==0: continue
            if bal(a+[(-t)%M],M) and bal(b+[t],M): ok.append((a,b,t))
        print(M,A,'3+3 decompositions:',ok)
