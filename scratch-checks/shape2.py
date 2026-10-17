from itertools import product
for p in (5,7,11,13):
    reps=[v for v in range(1,(p+1)//2)]
    seen={}
    for ch in product((1,-1),repeat=len(reps)):
        S=frozenset((v if c==1 else p-v) for v,c in zip(reps,ch))
        psi=lambda w:1 if w in S else -1
        nf=sum(1 for w in range(1,p) if psi(2*w%p)!=psi(w))
        W=sorted(w for w in range(1,p) if w not in S and (2*w)%p in S)
        tot=(p-1)//2+len(W)
        # orbit under units
        key=min(tuple(sorted((t*s)%p for s in S)) for t in range(1,p))
        if tot<=6: seen.setdefault(key,(sorted(S),W,nf))
    print(p,list(seen.values()))
