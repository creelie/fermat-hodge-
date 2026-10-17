from math import gcd
from itertools import combinations_with_replacement as cwr
def bal(A,M): return [t for t in range(1,M) if gcd(t,M)==1 and sum((t*a)%M for a in A)!=3*M]
def pair(A,M):
    from collections import Counter
    c=Counter(A); return any(c[(-y)%M]>(1 if (-y)%M==y else 0) for y in c)
def split(A,M):
    from itertools import combinations
    return any((a+b+c)%M==0 and (sum(A)-a-b-c)%M==0 for a,b,c in combinations(A,3))
cases={'a20':(20,[1,17,12]),'c28':(28,[1,9,25]),'e28':(28,[1,9,17,16,20]),'g44':(44,[1,13,37,41,5,24])}
for k,(M,loc) in cases.items():
    low=[M//4,M//2,3*M//4]
    for c in cwr(low,6-len(loc)):
        A=sorted(loc+list(c))
        print(k,A,'sum%M=',sum(A)%M,'pair' if pair(A,M) else '', 'split' if split(A,M) else '', 'badunits',bal(A,M)[:3])
