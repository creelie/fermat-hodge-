"""sextic_cubic_fields.py -- the computation of Remark VI (no exclusion over twelve cubic fields).
Integral classes of the flat secant space S(0,q) of the sextic CM field F = F_0(sqrt(-q))
for every totally real cubic field F_0 of discriminant below 500 (twelve fields; polynomial
discriminant equals the field discriminant, so O = Z[alpha]), q in {1, k + alpha}:
the lattice, the Gram matrix of -chi/8, the least -chi on a nonzero class, the number of
classes with -chi <= 24 (the bound of prop:sexticcount(iii)) and with -chi <= 32, and the
shape (N_w, r^2, r^3) of every class with -chi <= 32.  Exact, standard library.
"""
import sys, os, time, random
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sextic_lattice as S

FIELDS = [(49,[1,1,-2,-1]),(81,[1,0,-3,1]),(148,[1,-1,-3,1]),(169,[1,-1,-4,-1]),
          (229,[1,0,-4,1]),(257,[1,-1,-4,3]),(316,[1,-1,-4,2]),(321,[1,-1,-4,1]),
          (361,[1,-1,-6,7]),(404,[1,-1,-5,-1]),(469,[1,-1,-5,4]),(473,[1,0,-5,-1])]

def gram(poly, qvec, Lb):
    return [[-(S.chi_formula(poly, qvec, [x+y for x, y in zip(Lb[i], Lb[j])])
               - S.chi_formula(poly, qvec, Lb[i]) - S.chi_formula(poly, qvec, Lb[j]))/16
             for j in range(8)] for i in range(8)]

EXPECT = {49: (32, 32), 81: (32, 32), 148: (32, 288), 169: (32, 384), 229: (32, 912), 257: (32, 352),
          316: (32, 480), 321: (32, 600), 361: (32, 960), 404: (32, 544), 469: (32, 2400), 473: (32, 1208)}
fails = 0
random.seed(20261021)
only = [int(a) for a in sys.argv[1:]]
for D, poly in FIELDS:
    if only and D not in only: continue
    rr = sorted(z.real for z in S.durand_kerner(poly))
    k = int(-min(rr)) + 1
    for which, qvec in enumerate(([1,0,0], [k,1,0])):
        t0 = time.time()
        qs = [sum(c*r**e for e, c in enumerate(qvec)) for r in rr]
        assert all(v > 0 for v in qs)
        monos, A = S.coefficient_matrix(poly, qvec)
        Lb = S.integral_lattice(A)
        S.check_chi_direct(poly, qvec, Lb, trials=2)
        G = gram(poly, qvec, Lb)
        assert all(v.denominator == 1 for row in G for v in row), "Gram not integral"
        dens = sorted(set(v.denominator for row in Lb for v in row))
        sv24 = S.short_vectors(G, 3)
        sv32 = S.short_vectors(G, 4)
        p = S.shape_prime(poly, qvec, 10**6)
        tally = {}
        for x in sv32:
            co = [sum(Fr(x[b])*Lb[b][i] for b in range(8)) for i in range(8)]
            chi = S.chi_formula(poly, qvec, co)
            Nw, Asum, rho, Msum, r2, r3 = S.shape_invariants(poly, qvec, co, p)
            key = (int(chi), Nw, r2, r3); tally[key] = tally.get(key, 0) + 1
        # least -chi: search outward
        bound = 4
        while not S.short_vectors(G, bound): bound += 1
        print(f"disc {D} poly {poly} q={qvec}: denominators {dens}; classes with -chi<=24: {len(sv24)}; "
              f"with -chi<=32: {len(sv32)}; least -chi = {8*bound}; shapes(chi,N_w,r2,r3): {tally}; "
              f"{time.time()-t0:.1f}s", flush=True)
        ok = len(sv24) == 0 and 8*bound == EXPECT[D][which]
        fails += not ok
        print("PASS" if ok else "FAIL", flush=True)
print("sextic_cubic_fields: PASS" if fails == 0 else f"sextic_cubic_fields: {fails} FAILED")
sys.exit(1 if fails else 0)
