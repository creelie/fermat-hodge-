import sys, math
from collections import defaultdict
from itertools import combinations_with_replacement as cwr
def primes_of(n):
    ps=[];d=2
    while d*d<=n:
        if n%d==0:
            ps.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:ps.append(n)
    return ps
class Lattice:
    # HNF-ish echelon basis over Z, rows dict pivot->row
    def __init__(self,dim): self.dim=dim; self.rows={}
    def reduce(self,v):
        v=list(v)
        for i in range(self.dim):
            if v[i]==0: continue
            if i not in self.rows: return v,i
            r=self.rows[i]
            if v[i]%r[i]==0:
                q=v[i]//r[i]; v=[a-q*b for a,b in zip(v,r)]
            else:
                return v,i
        return v,None
    def add(self,v):
        v=list(v)
        while True:
            # find first nonzero
            i=next((k for k in range(self.dim) if v[k]!=0),None)
            if i is None: return
            if i not in self.rows:
                if v[i]<0: v=[-a for a in v]
                self.rows[i]=v; return
            r=self.rows[i]
            if v[i]%r[i]==0:
                q=v[i]//r[i]; v=[a-q*b for a,b in zip(v,r)]; continue
            # gcd combine
            a,b=r[i],v[i]
            # extended gcd
            g,x,y=egcd(a,b)
            new=[x*p+y*q for p,q in zip(r,v)]
            other=[(b//g)*p-(a//g)*q for p,q in zip(r,v)]
            if new[i]<0: new=[-c for c in new]
            self.rows[i]=new
            v=other  # has zero at i
    def member(self,v):
        v=list(v)
        for i in range(self.dim):
            if v[i]==0: continue
            if i not in self.rows: return False
            r=self.rows[i]
            if v[i]%r[i]: return False
            q=v[i]//r[i]; v=[a-q*b for a,b in zip(v,r)]
        return True
def egcd(a,b):
    if b==0: return (a,1,0)
    g,x,y=egcd(b,a%b); return (g,y,x-(a//b)*y)
def setup(M):
    h=(M-1)//2
    idx={}
    for y in range(1,M):
        if y< M-y: idx[y]=(y-1,1)
        elif y>M-y: idx[y]=(M-y-1,-1)
    dim=h+(1 if M%2==0 else 0)
    def vec(A):
        v=[0]*dim
        for a in A:
            a%=M
            if a==0: raise ValueError
            if M%2==0 and a==M//2: v[h]+=1
            else:
                i,s=idx[a]; v[i]+=s
        return v
    L=Lattice(dim)
    if M%2==0:
        e=[0]*dim; e[h]=2; L.add(e)
    for l in primes_of(M):
        if l==2:
            for x in range(1,M):
                if (2*x)%M: L.add(vec([x,x+M//2,-2*x,M//2]))
        else:
            for x in range(1,M):
                if (l*x)%M: L.add(vec([x+k*(M//l) for k in range(l)]+[-l*x]))
    return L,vec
def balanced(M,size=6):
    U=[t for t in range(1,M) if math.gcd(t,M)==1]
    vecs={a:tuple((t*a)%M for t in U) for a in range(1,M)}
    target=tuple(size//2*M for _ in U)
    H=defaultdict(list)
    for T in cwr(range(1,M),size//2):
        s=tuple(map(sum,zip(*(vecs[a] for a in T))))
        H[s].append(T)
    seen=set()
    for s,Ts in H.items():
        r=tuple(x-y for x,y in zip(target,s))
        if r in H and s<=r:
            for T in Ts:
                for T2 in H[r]:
                    A=tuple(sorted(T+T2))
                    if A not in seen:
                        seen.add(A)
    return seen,U
def canon(A,U,M):
    return min(tuple(sorted((t*a)%M for a in A)) for t in U)
if __name__=="__main__":
    M=int(sys.argv[1]); size=int(sys.argv[2]) if len(sys.argv)>2 else 6
    L,vec=setup(M)
    S,U=balanced(M,size)
    orb=set(canon(A,U,M) for A in S)
    bad=[A for A in sorted(orb) if not L.member(vec(A))]
    print("M",M,"balanced",len(S),"orbits",len(orb),"outside S_M",len(bad))
    for A in bad[:12]: print("  ",A)
