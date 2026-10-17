# Every residual of at most three elements at p in {5,7,11,13} (glob/residuals_p.txt,
# level D*p) becomes balanced after adding T: one element tau (size 3) or
# {tau, N/2} (size 2), tau of order dividing D, and the orders in T are smaller
# than the largest order in B.  Prints T for each.
import math
from fractions import Fraction as F
def load(e):
    out=[]
    for line in open('glob/residuals_%d.txt'%e):
        a,b=line.split(':'); D,n=map(int,a.split())
        out.append((D,[int(t) for t in b.split()]))
    return out
def balanced(N,A):
    if sum(A)%N or any(a%N==0 for a in A): return False
    U=[t for t in range(1,N) if math.gcd(t,N)==1]
    vals={sum((t*a)%N for a in A) for t in U}
    return vals=={len(A)*N//2}
bad=0
for p in (5,7,11,13):
    for D,B in load(p):
        if len(B)>3: continue
        N=D*p; o=lambda y:N//math.gcd(y,N)
        found=[]
        for tau in range(p,N,p):
            T=[tau] if len(B)==3 else [tau,N//2]
            if len(B)==2 and N%2: continue
            if balanced(N,B+T) and max(o(y) for y in T)<max(o(b) for b in B):
                found.append(T)
        print(p,D,N,B,'orders',[o(b) for b in B],'T',found)
        if not found: bad+=1
print('without completion:',bad)
