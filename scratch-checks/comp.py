import sys, collections
# read movesG output files, report components without a base member
def analyse(fn):
    reps = {}; cur = None; edges = collections.defaultdict(set); base = set()
    for line in open(fn):
        w = line.split()
        if not w: continue
        if w[0] == 'R':
            cur = tuple(map(int, w[1:7])); reps[cur] = int(w[7])
            if int(w[7]): base.add(cur)
        elif w[0] == 'E':
            if w[1] in ('D', 'N', 'S'): base.add(cur)
            elif w[1] == 'X':
                b = tuple(map(int, w[2:8])); edges[cur].add(b); edges[b].add(cur)
    seen = set(); comps = []
    for r in reps:
        if r in seen: continue
        st = [r]; c = []; seen.add(r)
        while st:
            u = st.pop(); c.append(u)
            for v in edges[u]:
                if v not in seen: seen.add(v); st.append(v)
        comps.append(c)
    bad = [c for c in comps if not any(u in base for u in c)]
    return len(reps), len(comps), bad
for fn in sys.argv[1:]:
    n, nc, bad = analyse(fn)
    print(fn, 'orbits', n, 'components', nc, 'baseless', len(bad))
    for c in bad: print('   ', sorted(c)[:6], len(c))
