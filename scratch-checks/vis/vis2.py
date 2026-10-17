import sys, math
from vis import search
M=int(sys.argv[1])
sq=[a for a in range(1,M) if (a*a)%M==1]
inv={'nuR':lambda A: sum(1 for a in A if (a*a)%M==1)%2==1}
for k in [3,5,7,11,13,17,19,23]:
    if M%k==0 and (M//k)%k!=0:
        inv['nu%d'%k]=(lambda k: lambda A: sum(1 for a in A if math.gcd(a,M)==M//k)%2==1)(k)
for name,pr in inv.items():
    for size in (4,6):
        print(M,name,size,search(M,pr,size,2),flush=True)
