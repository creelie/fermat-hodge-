# Direct check at primes p >= 29: prop at D = 72 modulo p, comparison with the
# reductions of the formal configurations, chains at level L_B p (fchain).
# usage: direct.py primes_file outdir
import sys, subprocess, os
pf=sys.argv[1]; od=sys.argv[2]; os.makedirs(od,exist_ok=True)
H=os.path.dirname(os.path.abspath(__file__))
for line in open(pf):
    for t in line.split():
        p=int(t); fn=os.path.join(od,'P_3_2_%d.txt'%p)
        e=subprocess.run([os.path.join(H,'prop'),'3','2',str(p)],capture_output=True,text=True)
        open(fn,'w').write(e.stdout); st=e.stderr.strip().splitlines()[-1]
        sp=subprocess.run(['python3',os.path.join(H,'specialize.py'),'72',str(p),os.path.join(H,'F_3_2.txt'),fn],capture_output=True,text=True).stdout.strip()
        lc=subprocess.run(['python3',os.path.join(H,'levelchain.py'),'72',str(p),'2','fchain',fn],capture_output=True,text=True).stdout
        open(os.path.join(od,'C_3_2_%d.txt'%p),'w').write(lc)
        print(sp,'|',lc.splitlines()[0].split(' ',1)[1],flush=True)
