import sys, itertools, math
M=int(sys.argv[1]); A=list(map(int,sys.argv[2:8]))
U=[t for t in range(1,M) if math.gcd(t,M)==1]
def bal(B):
    s0=sum(B)
    if s0%M: return False
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
found=0
for i,j in itertools.combinations(range(6),2):
    a,b=A[i],A[j]
    for x in range(1,M):
        y=(-(a+b+x))%M
        if y==0 or y<x: continue
        sig=[a,b,x,y]
        if not bal(sig): continue
        rest=[A[k] for k in range(6) if k not in (i,j)]
        B=depair(rest+[(-x)%M,(-y)%M])
        tag=''
        if len(B)<=4: tag='direct'
        elif not gen(B): tag='nongen'
        elif split(B): tag='split'
        elif prof(B)<p0: tag='lower'
        else: tag='same/higher'
        print(sig,'->',sorted(B),prof(B),tag); found+=1
print('balanced 4-tuples through two elements:',found)
