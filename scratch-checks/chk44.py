from math import gcd
from itertools import combinations_with_replacement as cwr
M=44
U=[t for t in range(1,M) if gcd(t,M)==1]
o44=[y for y in range(1,M) if gcd(y,M)==1]
o11=[4*v for v in range(1,11)]
cnt=0
for c in cwr(o44,5):
  for z in o11:
    A=list(c)+[z]
    if sum(A)%M: continue
    if all(sum((t*a)%M for a in A)==3*M for t in U):
      s=set(A)
      if any((-a)%M in s for a in A): continue
      cnt+=1; print(sorted(A))
print('count',cnt)
