import sys, math
from collections import defaultdict
def units(M): return [t for t in range(1,M) if math.gcd(t,M)==1]
def search(M, pred, size=6, limit=5):
    U=units(M)
    vec={a:tuple((t*a)%M for t in U) for a in range(1,M)}
    target=tuple(size//2*M for _ in U)
    half=size//2
    from itertools import combinations_with_replacement as cwr
    H=defaultdict(list)
    for T in cwr(range(1,M),half):
        s=tuple(sum(c) for c in zip(*(vec[a] for a in T)))
        H[s].append(T)
    found=[]
    seen=set()
    for s,Ts in H.items():
        r=tuple(x-y for x,y in zip(target,s))
        if r in H:
            for T in Ts:
                for T2 in H[r]:
                    A=tuple(sorted(T+T2))
                    if A in seen: continue
                    seen.add(A)
                    if pred(A):
                        found.append(A)
                        if len(found)>=limit: return found
    return found
if __name__=="__main__":
    p=int(sys.argv[1]); M=3*p
    pred=lambda A: sum(1 for a in A if a%3==0)%2==1
    for size in (4,6):
        f=search(M,pred,size,3)
        print(M,size,f)
