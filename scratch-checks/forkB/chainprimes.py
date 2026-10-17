# Primes p >= 29 at which two formally distinct elements appearing in a formal
# chain (or in its configuration) coincide or become negatives of each other:
# (s1, e1 2^a1 3^b1), (s2, e2 2^a2 3^b2) with s1 = s2 and e1 2^a1 3^b1 = e2 2^a2 3^b2
# mod p, or s1 = -s2 and e1 2^a1 3^b1 = -e2 2^a2 3^b2 mod p.  Reads "elems" lines
# (DUMP=1 fchain.py at the level of the configuration).
import sys
def pf(n):
    out=set(); d=2
    while d*d<=n:
        while n%d==0: out.add(d); n//=d
        d+=1 if d==2 else 2
    if n>1: out.add(n)
    return out
D=int(sys.argv[1]); PR=set(); amax=bmax=0
for fn in sys.argv[2:]:
    for line in open(fn):
        if not line.startswith('  elems'): continue
        E=[]
        for t in line.split()[1:]:
            s,u=t.split(':'); sg,a,b=map(int,u.split(','))
            if sg: E.append((int(s),sg,a,b))
        for i in range(len(E)):
            for j in range(i+1,len(E)):
                s1,e1,a1,b1=E[i]; s2,e2,a2,b2=E[j]
                for same in (1,-1):
                    if (s1-same*s2)%D: continue
                    a=a1-a2; b=b1-b2; eps=e1*e2*same   # need 2^a 3^b = eps
                    if a==0 and b==0: continue
                    amax=max(amax,abs(a)); bmax=max(bmax,abs(b))
                    n=abs(2**max(a,0)*3**max(b,0)-eps*2**max(-a,0)*3**max(-b,0))
                    PR|=set(q for q in pf(n) if q>=29)
print('max |a|',amax,'max |b|',bmax,'primes',sorted(PR))
