# Sequential sweep (one core): locG then lchain2 for composite e' and D | 72.
# Usage: python3 sweep.py  (run from any directory; paths are absolute)
import subprocess, math, os, time
W = '/dev/shm/tmpb/forkC'
def phi(n):
    r = n; m = n; p = 2
    while p * p <= m:
        if m % p == 0:
            r -= r // p
            while m % p == 0: m //= p
        p += 1
    if m > 1: r -= r // m
    return r
COMP = [25, 35, 49, 55, 65, 77, 85, 91, 95, 115, 119, 121, 125, 143, 175, 245, 275, 385]
VW = [(v, w) for v in range(4) for w in range(3)]
jobs = set()
for e in COMP:
    for v, w in VW:
        D = 2**v * 3**w
        if D == 72 and phi(e) > 72: continue
        jobs.add((e, v, w))
def cost(j):
    e, v, w = j; ne = 2**v * 3**w * phi(e)
    pri = 0 if e in (35, 55) else 1
    if 2**v * 3**w == 72 and ne > 3000: return (3, ne)  # D = 72 extras last
    return (pri if ne <= 3000 else 2, ne)
jobs = sorted(jobs, key=cost)
log = open(W + '/sweep.log', 'a')
for e, v, w in jobs:
    D = 2**v * 3**w; N = D * e
    L = '%s/data/L_%d_%d_%d.txt' % (W, v, w, e); R = '%s/data/R_%d_%d_%d.txt' % (W, v, w, e)
    if os.path.exists(R) and os.path.getsize(R) > 0: continue
    t0 = time.time()
    with open(L, 'w') as fo, open(L + '.err', 'w') as fe:
        rc = subprocess.call([W + '/locG', str(e), str(v), str(w)], stdout=fo, stderr=fe)
    t1 = time.time()
    with open(R + '.tmp', 'w') as fo:
        rc2 = subprocess.call(['python3', W + '/lchain2.py', str(N), '2', L], stdout=fo)
    os.rename(R + '.tmp', R)
    t2 = time.time()
    last = open(L + '.err').read().strip().splitlines()[-1]
    head = open(R).readline().strip().split()
    log.write('e=%d D=%d N=%d rc=%d/%d loc=%.1fs chain=%.1fs | %s | total %s nochain %s\n' % (e, D, N, rc, rc2, t1 - t0, t2 - t1, last, head[2], head[4]))
    log.flush()
log.write('SWEEP DONE\n'); log.close()
