# Summarise sweep.log: for each composite e' and D = 2^v 3^w | 72, the number
# of local configurations found by locG and the number without a local chain
# (lchain2.py, depth 2).  Prints a markdown table; "-" = not run.
import re, sys
from collections import defaultdict
LOG = sys.argv[1] if len(sys.argv) > 1 else '/dev/shm/tmpb/forkC/sweep.log'
Ds = [1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72]
tot = defaultdict(dict); noc = defaultdict(dict)
for l in open(LOG):
    m = re.match(r'e=(\d+) D=(\d+) .*\| total (\d+) nochain (\d+)', l)
    if not m: continue
    e, D, t, n = map(int, m.groups())
    tot[e][D] = t; noc[e][D] = n
print('| e\' | ' + ' | '.join('D=%d' % D for D in Ds) + ' |')
print('|---|' + '---|' * len(Ds))
for e in sorted(tot):
    cells = []
    for D in Ds:
        if D in tot[e]:
            c = str(tot[e][D])
            if noc[e][D]: c += ' (%d)' % noc[e][D]
        else:
            c = '-'
        cells.append(c)
    print('| %d | ' % e + ' | '.join(cells) + ' |')
