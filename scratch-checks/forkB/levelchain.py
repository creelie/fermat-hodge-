# Chains at the level of the configuration itself.  For a configuration at level
# D p (D = 2^v 3^w, 6 | D), D_B is the 2,3-part of the lcm of its orders and
# L = lcm(D_B, 6); the configuration lies in the subgroup of order L p, and the
# chain is searched at level L p (moves T, sigma_3 there are those of every
# level M with L p | M).  Backend: lchain.py (any p, level L p as integers) or
# fchain.py (formal, or p >= 29).  Prints per (D_B, size) the totals and the
# configurations without a chain, rescaled to level D_B p (canonical over units).
# usage: levelchain.py D p DEPTH backend files...   backend = lchain | fchain
import sys, math, subprocess, os, tempfile
from collections import defaultdict, Counter
D=int(sys.argv[1]); P=int(sys.argv[2]); DEPTH=sys.argv[3]; BK=sys.argv[4]; files=sys.argv[5:]
HERE=os.path.dirname(os.path.abspath(__file__))
def lcm(a,b): return a*b//math.gcd(a,b)
def read(fn):
    out=[]
    for line in open(fn):
        w=line.split()
        if not w: continue
        if w[0]=='F': out.append([(int(t.split(',')[0]),tuple(map(int,t.split(',')[1:]))) for t in w[3:]])
        elif w[0]=='C': out.append([(int(t.split('/')[0])%D, int(t.split('/')[0])%P) for t in w[5:]])
    return out
def dof(s,Dd): return Dd//math.gcd(s,Dd)
def crt(s,u,L):
    return (s + L*(((u-s)*pow(L,-1,P))%P)) % (L*P)
tmp=tempfile.mkdtemp(dir=os.environ.get('TMPDIR','/dev/shm/tmpb'))
for fn in files:
    cf=read(fn); groups=defaultdict(list)
    for B in cf:
        DB=1
        for s,u in B: DB=lcm(DB,dof(s,D))
        L=lcm(DB,6); k=D//L
        if P: Bn=[(s//k, (u*pow(k,-1,P))%P) for s,u in B]
        else: Bn=[(s//k,u) for s,u in B]
        groups[L].append((DB,Bn))
    stat=Counter(); res=[]
    for L,lst in sorted(groups.items()):
        f=os.path.join(tmp,'g%d.txt'%L)
        with open(f,'w') as g:
            for DB,B in lst:
                if P: g.write('C n=%d c=0 d=0 : '%len(B)+' '.join('%d/%d'%(crt(s,u,L),dof(s,L)*P) for s,u in B)+'\n')
                else: g.write('F n=%d : '%len(B)+' '.join('%d,%d,%d,%d'%((s,)+u) for s,u in B)+'\n')
        if BK=='lchain': cmd=['python3',os.path.join('/dev/shm/tmpb/m6','lchain.py'),str(L*P),DEPTH,f]
        else: cmd=['python3',os.path.join(HERE,'fchain.py'),str(L),str(P),DEPTH,f]
        out=subprocess.run(cmd,capture_output=True,text=True).stdout
        if os.environ.get('OUTDIR'):
            open(os.path.join(os.environ['OUTDIR'],'%s.L%d.out'%(os.path.basename(fn),L)),'w').write(out)
        out=out.splitlines()
        bad=set()
        for line in out[1:]:
            if line.startswith('  chain') or line.startswith('  elems'): continue
            toks=line.split()
            if BK=='lchain': els=sorted(int(t.split('/')[0]) for t in toks); bad.add(tuple(els))
            else: bad.add(tuple(toks))
        for DB,B in lst:
            if BK=='lchain': key=tuple(sorted(crt(s,u,L) for s,u in B))
            else:
                if P: key=tuple(sorted(str(crt(s,u,L)) for s,u in B))
                else: key=tuple(sorted('%d:%s'%(s,','.join(map(str,u))) for s,u in B))
            nb = key in bad
            stat[(DB,len(B),'nochain' if nb else 'chain')]+=1
            if nb: res.append((DB,L,B))
    print(fn,'p=%d'%P,'configs',len(cf),'nochain',len(res))
    for k in sorted(stat): print('   D_B=%d size=%d %s %d'%(k+(stat[k],)))
    # residuals rescaled to level D_B p, canonical over units of Z/(D_B p) (p > 0)
    for DB,L,B in res:
        if P:
            k=L//DB; NN=DB*P
            xs=[crt(s,u,L)//k for s,u in B]
            U=[t for t in range(1,NN) if math.gcd(t,NN)==1]
            best=min(tuple(sorted(x*t%NN for x in xs)) for t in U)
            print('   residual D_B=%d level %d :'%(DB,NN),' '.join('%d/%d'%(x,NN//math.gcd(x,NN)) for x in best))
        else:
            print('   residual D_B=%d :'%DB,' '.join('%d:%s'%(s,','.join(map(str,u))) for s,u in B))
