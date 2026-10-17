# Supplementary sequential sweep (one core): further composite e' with a prime
# factor at most 23 (the open case (R) of the notes), at D = 6 and 12, and at
# D = 18 when 18 phi(e') <= 2880; and 841, 899 at D = 6 (formal regime).
# Same programs and files as sweep.py; log in sweep2.log.
# Usage: python3 sweep2.py
import subprocess, os, time
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
EXTRA = [133, 145, 155, 161, 169, 185, 187, 203, 205, 209, 215, 217, 221, 235,
         247, 253, 265, 289, 295, 305, 325, 343, 361, 425, 455, 475, 539, 595,
         605, 625, 715, 1001,
         841, 899]   # 841 = 29^2 (in E_comp), 899 = 29 31 (not): cross-checks of C11
jobs = []
for e in EXTRA:
    for v, w in [(1, 1), (2, 1), (1, 2)]:
        ne = 2**v * 3**w * phi(e)
        if (v, w) == (2, 1) and ne > 2880: continue
        if (v, w) == (1, 2) and ne > 2880: continue
        jobs.append((ne, e, v, w))
jobs.sort(key=lambda j: (j[1] not in (841, 899), j[0]))   # the C11 cross-checks first
log = open(W + '/sweep2.log', 'a')
for ne, e, v, w in jobs:
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
