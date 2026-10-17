import sys, math
from wm import setup, balanced, canon
M=int(sys.argv[1])
L,vec=setup(M)
S,U=balanced(M)
orb=sorted(set(canon(A,U,M) for A in S))
bad=[A for A in orb if not L.member(vec(A))]
print("M",M,"orbits",len(orb),"outside S_M",len(bad),flush=True)
# images from proper divisors
divs=[d for d in range(3,M) if M%d==0]
imgs=[]
for d in divs:
    Ld,vecd=setup(d)
    Sd,Ud=balanced(d)
    od=set(canon(A,Ud,d) for A in Sd)
    bd=[A for A in od if not Ld.member(vecd(A))]
    g=M//d
    for A in bd: imgs.append(tuple(sorted(g*a for a in A)))
    print("  divisor",d,"outside",len(bd),flush=True)
for B in imgs: L.add(vec(B))
still=[A for A in bad if not L.member(vec(A))]
print("M",M,"not explained by lower levels:",len(still))
for A in still[:10]: print("   ",A)
