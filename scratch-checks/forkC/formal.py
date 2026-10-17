# For each local configuration (lines "C ..." of an L file at level N = D e'),
# compute the relation functions Gamma_psi on U = (Z/e')^x, one for every
# primitive character psi mod f, f | D (the relations at conductors f e'):
#   x = ((D/d) alpha, b) in Z/D x U with x/N = a/D + b/e' (mod 1), d = type,
#   Gamma_psi = sum_{x : f | d} (phi(D)/phi(d)) psi(alpha) delta_{d b}
#               * prod_{l | d, l not | f} (delta_1 - conj psi(l) delta_{1/l}),
# and its part of parity eps = -psi(-1).  The relation says that this part is
# split along the K_p.  "formal" means every such part vanishes identically.
# usage: python3 formal.py e' v w Lfile
import sys, math, cmath
from collections import defaultdict
e = int(sys.argv[1]); v = int(sys.argv[2]); w = int(sys.argv[3]); fn = sys.argv[4]
D = 2**v * 3**w; N = D * e
def phi(n): return sum(1 for k in range(1, n + 1) if math.gcd(k, n) == 1)
U = [u for u in range(e) if math.gcd(u, e) == 1]
inv = lambda a, m: pow(a, -1, m)
# characters mod f: build from generators via brute force (f <= 72)
def chars(f):
    G = [g for g in range(1, f + 1) if math.gcd(g, f) == 1] if f > 1 else [1]
    if f == 1: return [{0: 1}]  # trivial
    # group exponent
    out = []
    # brute force: homomorphisms to roots of unity of order dividing lcm
    lam = 1
    for g in G:
        o = 1; y = g % f
        while y != 1 % f: y = y * g % f; o += 1
        lam = lam * o // math.gcd(lam, o)
    # pick a generating set greedily and assign roots
    gens = []
    sub = {1 % f}
    for g in G:
        if g % f not in sub:
            gens.append(g % f)
            new = set(sub)
            frontier = list(sub)
            while frontier:
                y = frontier.pop()
                for h in gens:
                    z = y * h % f
                    if z not in new: new.add(z); frontier.append(z)
            sub = new
    import itertools
    ords = []
    for g in gens:
        o = 1; y = g
        while y != 1 % f: y = y * g % f; o += 1
        ords.append(o)
    res = []
    for ks in itertools.product(*[range(lam) for _ in gens]):
        # define on words; check well-defined
        val = {}
        ok = True
        words = [(1 % f, [0] * len(gens))]
        val[1 % f] = 0
        frontier = [1 % f]
        while frontier and ok:
            y = frontier.pop()
            for i, h in enumerate(gens):
                z = y * h % f; vz = (val[y] + ks[i]) % lam
                if z in val:
                    if val[z] != vz: ok = False; break
                else: val[z] = vz; frontier.append(z)
        if ok: res.append({g: cmath.exp(2j * math.pi * val[g] / lam) for g in val})
    # dedupe
    uniq = []
    for c in res:
        key = tuple(round(c[g].real, 6) + 1j * round(c[g].imag, 6) for g in sorted(c))
        if key not in [u[0] for u in uniq]: uniq.append((key, c))
    return [c for _, c in uniq]
def primitive(c, f):
    for l in (2, 3):
        if f % l == 0:
            g = f // l
            # trivial on {k = 1 mod g}?
            if all(abs(c[k] - 1) < 1e-9 for k in c if (k - 1) % g == 0): return False
    return True
divs = [d for d in range(1, D + 1) if D % d == 0]
psis = []
for f in divs:
    if f % 4 == 2: continue
    for c in chars(f):
        if primitive(c, f): psis.append((f, c))
def analyse(B):
    els = []
    for x in B:
        # a/D + b/e' = x/N  ->  a = x * inv(e', D) mod D, b = x * inv(D, e') mod e'
        a = x * inv(e % D, D) % D if D > 1 else 0
        b = x * inv(D % e, e) % e
        d = D // math.gcd(a, D)
        alpha = (a // (D // d)) % d if d > 1 else 0
        els.append((d, alpha, b))
    nz = []
    for f, c in psis:
        G = defaultdict(complex)
        for d, alpha, b in els:
            if d % f: continue
            wgt = phi(D) // phi(d) * (c[alpha % f] if f > 1 else 1)
            terms = {d * b % e: wgt}
            for l in (2, 3):
                if d % l == 0 and f % l:
                    cl = c[l % f] if f > 1 else 1
                    new = defaultdict(complex)
                    for u, val in terms.items():
                        new[u] += val
                        new[u * inv(l, e) % e] -= cl.conjugate() * val
                    terms = new
            for u, val in terms.items(): G[u] += val
        eps = -(c[(-1) % f] if f > 1 else 1)
        eps = round(eps.real)
        part = {u: (G[u] + eps * G[(-u) % e]) / 2 for u in U}
        mass = sum(abs(z) for z in part.values())
        if mass > 1e-6: nz.append((f, round(mass, 3), sum(1 for z in part.values() if abs(z) > 1e-6)))
    return els, nz
for line in open(fn):
    t = line.split()
    if not t or t[0] != 'C': continue
    B = [int(s.split('/')[0]) for s in t[5:]]
    els, nz = analyse(B)
    tag = 'formal' if not nz else 'NONFORMAL'
    print(tag, ' '.join(t[1:4]), '|', ' '.join(t[5:]), '|', nz[:6])
