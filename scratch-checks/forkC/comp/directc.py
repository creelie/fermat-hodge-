# Direct check at the composite candidate exceptional e' (candcomp.py list):
# propc at D = 72 modulo e', comparison with the reductions of the 16 formal
# configurations (specializec.py), chains at level D_B e' (levelchainc.py with
# LEVEL=DB, backend fchainc.py).  One line per e' in the log.
# usage: directc.py list_file outdir
import sys, subprocess, os
lf = sys.argv[1]; od = sys.argv[2]; os.makedirs(od, exist_ok=True)
H = os.path.dirname(os.path.abspath(__file__))
env = dict(os.environ, LEVEL='DB', TMPDIR=os.path.join(H, 'tmp'))
for line in open(lf):
    for t in line.split():
        e = int(t); fn = os.path.join(od, 'P_3_2_%d.txt' % e)
        r = subprocess.run([os.path.join(H, 'propc'), '3', '2', str(e)], capture_output=True, text=True)
        open(fn, 'w').write(r.stdout); st = r.stderr.strip().splitlines()[-1]
        sp = subprocess.run(['python3', os.path.join(H, 'specializec.py'), '72', str(e), os.path.join(H, 'F_3_2.txt'), fn],
                            capture_output=True, text=True).stdout.strip()
        lc = subprocess.run(['python3', os.path.join(H, 'levelchainc.py'), '72', str(e), '2', 'fchain', fn],
                            capture_output=True, text=True, env=env).stdout
        open(os.path.join(od, 'C_3_2_%d.txt' % e), 'w').write(lc)
        print(sp, '|', lc.splitlines()[0].split(' ', 1)[1], '|', st.split('solutions=')[1], flush=True)
