# candidate exceptional primes p >= 29: 2^a 3^b = +-1 mod p for some (a,b) != 0
# with |a| <= A, |b| <= B; equivalently p | 2^a 3^b -+ 1 or p | 2^a -+ 3^b (a,b >= 0).
import sys
A=int(sys.argv[1]); B=int(sys.argv[2]); lo=int(sys.argv[3]) if len(sys.argv)>3 else 29
def pf(n):
    out=set(); d=2
    while d*d<=n:
        while n%d==0: out.add(d); n//=d
        d+=1 if d==2 else 2
    if n>1: out.add(n)
    return out
P=set()
for a in range(A+1):
    for b in range(B+1):
        if a==0 and b==0: continue
        for n in (2**a*3**b-1, 2**a*3**b+1, abs(2**a-3**b), 2**a+3**b):
            if n>1: P|=pf(n)
P=sorted(q for q in P if q>=lo)
print(len(P), P[:40], max(P))
