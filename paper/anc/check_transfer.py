"""Exact finite identities used by the new transfer constructions.

No finite check proves existence of cycles or either universal Hodge statement.
"""
from fractions import Fraction as F
from math import factorial, lcm
from random import Random

def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def mul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def sub(a,b):return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def inverse(a):
    n=len(a); m=[[F(x) for x in row]+e for row,e in zip(a,eye(n))]
    for j in range(n):
        k=next(i for i in range(j,n) if m[i][j]);m[j],m[k]=m[k],m[j]
        d=m[j][j];m[j]=[x/d for x in m[j]]
        for i in range(n):
            if i!=j:
                d=m[i][j];m[i]=[x-d*y for x,y in zip(m[i],m[j])]
    return [row[n:] for row in m]
def det(a):
    n=len(a)
    if n==1:return a[0][0]
    return sum((-1)**j*a[0][j]*det([row[:j]+row[j+1:] for row in a[1:]]) for j in range(n))

rng=Random(731)
cases=0
for n in range(1,6):
    for k in range(1,5):
        for trial in range(10):
            q=[[F((i+2)*(-1 if i else 1)) if i==j else F(0) for j in range(n)] for i in range(n)]
            b=[[F(rng.randrange(-3,4)) for _ in range(n)] for _ in range(k)]
            c=[[F(rng.randrange(-3,4)) for _ in range(k)] for _ in range(n)]
            v=eye(n)+b
            left=sub(q,mul(c,b))
            rows=[r+s for r,s in zip(left,c)]
            assert mul(rows,v)==q
            p=mul(mul(v,inverse(q)),rows)
            assert mul(p,p)==p and mul(p,v)==v
            assert mul(rows,sub(eye(n+k),p))==[[F(0)]*(n+k) for _ in range(n)]
            cases+=1
print(f'PASS: divisor-projector identities ({cases} rational matrix cases)')

cases=0
for n in range(1,9):
    for trial in range(20):
        values=[F(1)]+[F(rng.randrange(-4,5)) for _ in range(n-1)]
        t=[[values[j-i] if j>=i else F(0) for j in range(n)] for i in range(n)]
        x=[[F(rng.randrange(-5,6))] for _ in range(n)]
        y=mul(t,x)
        recovered=[[F(0)] for _ in range(n)]
        for j in range(n-1,-1,-1):
            recovered[j][0]=y[j][0]-sum(values[k-j]*recovered[k][0] for k in range(j+1,n))
        assert recovered==x
        cases+=1
print(f'PASS: projective-bundle triangular inverse ({cases} rational matrix cases)')

cases=0
for n in range(1,5):
    for k in range(1,5):
        d=F(n+k+1)
        b=[[F(rng.randrange(-3,4)) for _ in range(n)] for _ in range(k)]
        a=eye(n)+b
        c=[[F(rng.randrange(-3,4)) for _ in range(k)] for _ in range(n)]
        first=sub([[d*x for x in row] for row in eye(n)],mul(c,b))
        trace=[r+s for r,s in zip(first,c)]
        assert mul(trace,a)==[[d*x for x in row] for row in eye(n)]
        e=[[x/d for x in row] for row in mul(a,trace)]
        assert mul(e,e)==e and mul(e,a)==a
        assert mul(trace,sub(eye(n+k),e))==[[F(0)]*(n+k) for _ in range(n)]
        cases+=1
print(f'PASS: finite-cover trace splitting ({cases} rational matrix cases)')

cases=0
for b in range(1,4):
    for trial in range(50):
        a=[[rng.randrange(-2,3) for _ in range(b)] for _ in range(b)]
        da=det(a)
        if not da:continue
        gamma=[[F(rng.randrange(-6,7),3)] for _ in range(b)]
        bound=factorial(b)*2**b
        denominator=3*lcm(*range(1,bound+1))
        coefficients=mul(inverse(a),gamma)
        assert mul(a,coefficients)==gamma
        for row in coefficients:
            q=row[0]
            assert abs(q)<=factorial(b)*2*2**(b-1)
            assert denominator%q.denominator==0
        cases+=1
print(f'PASS: bounded-coordinate denominator estimate ({cases} exact systems)')
print('Scope: exact finite identities only; F2, F3-prime and full HC are not proved by these checks.')
