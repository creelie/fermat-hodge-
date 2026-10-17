# Compare the configurations found by prop modulo p (D = 72) with the reductions
# of the formal configurations: reduce u = sg 2^a 3^b mod p, drop reductions that
# fail a filter, canonicalize as prop does (lex-min over base and units of Z/D).
# usage: specialize.py D p formal_file modp_file
import sys, math
D=int(sys.argv[1]); P=int(sys.argv[2]); ff=sys.argv[3]; fm=sys.argv[4]
UD=[t for t in range(1,D+1) if math.gcd(t,D)==1]
def g_(s): return math.gcd(s,D)
def d_(s): return D//math.gcd(s,D)
def canon(B):
    best=None
    for (si,ui) in B:
        gi=g_(si)%D; iu=pow(ui,-1,P)
        for t in UD:
            if (t*si)%D!=gi: continue
            k=tuple(sorted(((t*s)%D)*P+(u*iu)%P for s,u in B))
            if best is None or k<best: best=k
    return best
def filt(B):
    n=len(B)
    for i in range(n):
        for j in range(n):
            if i==j: continue
            (s1,u1),(s2,u2)=B[i],B[j]
            if (s1+s2)%D==0 and (u1+u2)%P==0: return False
            if D%2==0 and u1==u2 and (s1+D//2)%D==s2: return False
            if D%3==0 and d_(s1)%3==0 and u1==u2 and s1!=s2 and d_(s1)==d_(s2) and (s1-s2)%(D//3)==0: return False
    return True
F=[]
for line in open(ff):
    w=line.split()
    if w and w[0]=='F':
        B=[]
        for t in w[3:]:
            s,sg,a,b=map(int,t.split(','))
            u=(sg*pow(2,a,P)*pow(3,b,P))%P if a>=0 and b>=0 else (sg*pow(2,a%(P-1),P)*pow(3,b%(P-1),P))%P
            B.append((s,u))
        F.append(B)
M=[]
for line in open(fm):
    w=line.split()
    if w and w[0]=='C': M.append([(int(t.split('/')[0])%D,int(t.split('/')[0])%P) for t in w[5:]])
FS=set(canon(B) for B in F if filt(B)); MS=set(canon(B) for B in M)
print('p=%d formal %d reductions_ok %d modp %d extra %d missing %d'%(P,len(F),len(FS),len(MS),len(MS-FS),len(FS-MS)))
