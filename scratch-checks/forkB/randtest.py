# random multisets of p-elements at level N = D p: compare lchain.py and fchain.py verdicts
import random, subprocess, sys, math
D=int(sys.argv[1]); p=int(sys.argv[2]); n=int(sys.argv[3]); seed=int(sys.argv[4])
random.seed(seed); N=D*p
els=[x for x in range(N) if x%p]
with open('rt.txt','w') as f:
    for _ in range(n):
        k=random.randint(2,6); B=[random.choice(els) for _ in range(k)]
        # bias: include structured ones (T-related, sigma3-related)
        if random.random()<0.5:
            y=random.choice(els); B=[y,(-2*y)%N]+B[:3]
        f.write('C n=%d c=0 d=0 : '%len(B)+' '.join('%d/%d'%(x,N//math.gcd(x,N)) for x in B)+'\n')
a=subprocess.run(['python3','/dev/shm/tmpb/m6/lchain.py',str(N),'2','rt.txt'],capture_output=True,text=True).stdout
b=subprocess.run(['python3','fchain.py',str(D),str(p),'2','rt.txt'],capture_output=True,text=True).stdout
def bad(out):
    S=set()
    for line in out.splitlines()[1:]:
        S.add(tuple(sorted(int(t.split('/')[0]) if '/' in t else int(t) for t in line.split())))
    return out.splitlines()[0], S
la,sa=bad(a); lb,sb=bad(b)
print('lchain:',la); print('fchain:',lb); print('same residual sets:', sa==sb)
