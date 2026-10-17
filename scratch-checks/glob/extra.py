# Further moves for sextuples without a chain of standard moves:
#  (g4) a balanced 4-tuple {a, b, x, y} through two elements a, b of A
#       (algebraic, as a Hodge class on a Fermat surface), giving
#       A - a - b + (-x) + (-y);
#  (dec) A = {a1,a2,a3} + {b1,b2,b3} with {a's, -t} and {b's, t} balanced.
# usage: extra.py M a1 ... a6   or   extra.py -f file (lines "M a1..a6")
import sys, itertools, math
def run(M,A):
    U=[t for t in range(1,M) if math.gcd(t,M)==1]
    def bal(B):
        h=None
        for t in U:
            s=sum((t*b)%M for b in B)
            if h is None: h=s
            elif s!=h: return False
        return True
    def order(y): return M//math.gcd(y,M)
    def prof(B): return sorted([order(b) for b in B],reverse=True)
    def depair(B):
        B=list(B); out=[]
        while B:
            x=B.pop()
            if (-x)%M in B: B.remove((-x)%M)
            else: out.append(x)
        return out
    def split(B):
        for i in range(1,6):
            for j in range(i+1,6):
                if (B[0]+B[i]+B[j])%M==0: return True
        return False
    def gen(B):
        g=M
        for b in B: g=math.gcd(g,b)
        return g==1
    p0=prof(A)
    for tr in itertools.combinations(range(6),3):
        if 0 not in tr: continue
        a=[A[i] for i in tr]; b=[A[i] for i in range(6) if i not in tr]
        t=sum(a)%M
        if t==0: continue
        if sum(x for x in a+[(-t)%M])%M==0 and bal(a+[(-t)%M]) and bal(b+[t]):
            return ('dec',a,b,t)
    for i,j in itertools.combinations(range(6),2):
        a,b=A[i],A[j]
        for x in range(1,M):
            y=(-(a+b+x))%M
            if y==0 or y<x: continue
            sig=[a,b,x,y]
            if not bal(sig): continue
            rest=[A[k] for k in range(6) if k not in (i,j)]
            B=depair(rest+[(-x)%M,(-y)%M])
            if len(B)<=4: return ('g4-direct',sig,B)
            if not gen(B): return ('g4-nongen',sig,B)
            if split(B): return ('g4-split',sig,B)
            if prof(B)<p0: return ('g4-lower',sig,B)
    return None
if sys.argv[1]=='-f':
    for line in open(sys.argv[2]):
        w=list(map(int,line.split()))
        if len(w)<7: continue
        print(w[0],w[1:7],run(w[0],w[1:7]))
else:
    M=int(sys.argv[1]); A=list(map(int,sys.argv[2:8])); print(M,A,run(M,A))
