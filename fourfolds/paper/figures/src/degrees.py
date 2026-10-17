# Classify the degrees M <= LIMIT for fig_degrees: earlier results, new (6 does not
# divide M), open (6 divides M), or 110 | M.  Writes degrees_data.tex.
import sys
LIMIT=int(sys.argv[1]) if len(sys.argv)>1 else 480
def fac(n):
    f={};p=2
    while p*p<=n:
        while n%p==0: f[p]=f.get(p,0)+1; n//=p
        p+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def known(M):
    f=fac(M); P=set(f)
    if M<=100 or M%2: return True
    if M<=250 and M not in (110,114,220,228): return True
    if len(P)<=1: return True
    if P<= {2,3,5,7} and (5 not in P or 7 not in P or M%420): return True
    if len(P)==2 and f.get(2,0)==1: return True
    if P<= {2,3,11} or P<= {2,3,13}: return True
    if (P<= {2,3,17} or P<= {2,3,19}) and f.get(2,0)<=1: return True
    return False
cls={}
for M in range(1,LIMIT+1):
    if M%110==0: cls[M]='x'
    elif known(M): cls[M]='k'
    elif M%6: cls[M]='a'
    else: cls[M]='b'
from collections import Counter
print(Counter(cls.values()))
with open('degrees_data.tex','w') as f:
    f.write('\\def\\degreedata{'+','.join('%d/%s'%(M,cls[M]) for M in range(1,LIMIT+1))+'}\n')
