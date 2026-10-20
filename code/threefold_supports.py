"""Exact checks for the support results at the CM point A_0 = E_0^6 (Section VI.H of
Bhattacharjee-Bhattacharya 2026, doi:10.5281/zenodo.23461752): the vectors of T D_h and their
images in H^1 of the threefolds, the four points where two threefolds of one family meet, the
threefolds through a general curve, the weights of the classes [Z_x], the Fourier inversion
on the four orbits, the weight spaces of H^4 and H^6, and the line of four threefolds of Lemma VI.32 with the
relations mu_a = m a^2 and the vanishing of sum_x sigma(x)^2 [Z_x] (Theorem VI.33).

Conventions.  E_0 = C/Z[i]; on the j-th factor B_j = E_0^2 with coordinates (u, v) = (z_j, z_{3+j})
the curve C_zeta is u + zeta v = 0; Z_x = C_{x_1} x C_{x_2} x C_{x_3}.  A vector of T D_h is
v = sum v_{lb} dzbar_b (x) d/dz_l with v_{3+m,b} = Y_{mb}, v_{b,3+m} = (h_{3+m}/h_b) Y_{mb} for
m, b <= 3 and all other entries zero, Y any 3 x 3 matrix.  The classes a_j, b_j, c_j, cbar_j of
H^2(B_j) are the classes of dz_j dzbar_j, dz_{3+j} dzbar_{3+j}, dz_j dzbar_{3+j}, dzbar_j dz_{3+j}
up to the normalisation of Appendix B, and the weight grading gives dz_j, dzbar_{3+j} weight e_j.

    python3 -I threefold_supports.py
"""
from __future__ import annotations

import itertools
import random
import sys
from fractions import Fraction

import sympy as sp

I = sp.I
MU4 = [sp.Integer(1), I, sp.Integer(-1), -I]
checks = []


def check(name, ok):
    checks.append((name, bool(ok)))
    print(f"{'PASS' if ok else 'FAIL'}  {name}")


def tdh_vector(Y, h):
    """the 6 x 6 matrix v[l][b] of the vector of T D_h with matrix Y (indices 0..5)"""
    v = [[sp.Integer(0)] * 6 for _ in range(6)]
    for m in range(3):
        for b in range(3):
            v[3 + m][b] = Y[m][b]
            v[b][3 + m] = h[3 + m] / h[b] * Y[m][b]
    return v


def kappa_component(v, zeta, k, j, sign):
    """coefficient of dzbar_j in dn_k(v) restricted to the curve C_{sign zeta_j} x {y}:
    dn_k = dz_k + zeta_k dz_{3+k}, and on C_{s zeta_j} one has dzbar_{3+j} = -s zeta_j dzbar_j."""
    form = [v[k][b] + zeta[k] * v[3 + k][b] for b in range(6)]      # coefficients of dzbar_b
    return sp.expand(form[j] - sign * zeta[j] * form[3 + j])


# ---------------------------------------------------------------- checks 1, 2: the classes kappa_T(v)_k on the curves
random.seed(7)
h = [sp.Rational(random.randint(1, 9), random.randint(1, 9)) for _ in range(6)]
ok1 = ok2 = True
for zeta in itertools.product(MU4, repeat=3):
    for j in range(3):
        for k in range(3):
            if k == j:
                continue
            Y = [[sp.Integer(random.randint(-3, 3)) for _ in range(3)] for _ in range(3)]
            v = tdh_vector(Y, h)
            got = kappa_component(v, zeta, k, j, +1)
            want = sp.expand(zeta[k] * Y[k][j] - zeta[j] * h[3 + j] / h[k] * Y[j][k])
            ok1 &= sp.simplify(got - want) == 0
            gotp = kappa_component(v, zeta, k, j, -1)
            wantp = sp.expand(zeta[k] * Y[k][j] + zeta[j] * h[3 + j] / h[k] * Y[j][k])
            ok2 &= sp.simplify(gotp - wantp) == 0
            E = [[sp.Integer(1 if (a, b) == (j, k) else 0) for b in range(3)] for a in range(3)]
            vE = tdh_vector(E, h)
            ok1 &= sp.simplify(kappa_component(vE, zeta, k, j, +1) + zeta[j] * h[3 + j] / h[k]) == 0
            ok2 &= sp.simplify(kappa_component(vE, zeta, k, j, -1) - zeta[j] * h[3 + j] / h[k]) == 0
check("kappa_T(v)_k on Gamma_y is (zeta_k Y_kj - zeta_j h_{3+j}/h_k Y_jk) dzbar_j, equal to -zeta_j h_{3+j}/h_k at Y = E_jk, for all 64 zeta and j != k", ok1)
check("kappa_T'(v)_k on Gamma'_y is (zeta_k Y_kj + zeta_j h_{3+j}/h_k Y_jk) dzbar_j, nonzero at Y = E_jk", ok2)

# ---------------------------------------------------------------- check 3: C_u and C_{-u} meet in the four points of order two
HALF = [sp.Rational(a, 2) + sp.Rational(b, 2) * I for a in range(2) for b in range(2)]   # (1/2)Z[i] / Z[i]


def in_lattice(z):
    z = sp.expand(z)
    return sp.re(z).is_integer and sp.im(z).is_integer


ok3 = True
for u in MU4:
    pts = [(a, b) for a in HALF for b in HALF if in_lattice(a + u * b)]
    ok3 &= len(pts) == 4 and all(in_lattice(a - u * b) for (a, b) in pts)
    # every point of C_u with 2x = 0 is one of them, and conversely
    ok3 &= set(a for (a, b) in pts) == set(HALF)
check("C_u and C_{-u} meet exactly in the four points of order two of C_u (|2u|^2 = 4), for every u", ok3)

# ---------------------------------------------------------------- check 4: the coordinates n'_j on C_{zeta_j} and n_j on C_{-zeta_j}
z = sp.symbols('z')
ok4 = True
for zeta in MU4:
    zc = sp.conjugate(zeta)
    ok4 &= sp.simplify((z - zeta * (-zc * z)) - 2 * z) == 0      # n' on C_zeta: z_{3+j} = -conj(zeta) z_j
    ok4 &= sp.simplify((z + zeta * (zc * z)) - 2 * z) == 0       # n on C_{-zeta}: z_{3+j} = conj(zeta) z_j
    ok4 &= sp.simplify((z + zeta * (-zc * z))) == 0              # n vanishes on C_zeta
check("n'_j restricts to 2 z_j on C_{zeta_j} and n_j to 2 z_j on C_{-zeta_j}", ok4)

# ---------------------------------------------------------------- check 5: the threefolds through a general Gamma_y
ok5 = True
for zeta in itertools.product(MU4, repeat=3):
    for j in range(3):
        k, l = [m for m in range(3) if m != j]
        meeting = [xi for xi in itertools.product(MU4, repeat=3) if xi[k] == zeta[k] and xi[l] == zeta[l]]
        ok5 &= len(meeting) == 4
        fam = [xi for xi in meeting if sp.expand((xi[0] * xi[1] * xi[2]) ** 2) == 1]
        zj = list(zeta); zj[j] = -zeta[j]
        if sp.expand((zeta[0] * zeta[1] * zeta[2]) ** 2) == 1:        # zeta in the family sigma = +-1
            ok5 &= sorted(map(str, fam)) == sorted(map(str, [tuple(zeta), tuple(zj)]))
        else:                                                            # otherwise the two of that family have xi_j = +-i zeta_j
            other = [tuple(s * zeta[m] if m == j else zeta[m] for m in range(3)) for s in (I, -I)]
            ok5 &= sorted(map(str, fam)) == sorted(map(str, other))
check("the threefolds meeting a general Gamma_y are the four with xi_k = zeta_k, xi_l = zeta_l; among the thirty-two of the family of zeta only Z_zeta and Z_zeta^(j), and for zeta of the other family the two with xi_j = +-i zeta_j", ok5)

# ---------------------------------------------------------------- check 6: the coefficient of X_eps in [Z_x]
a = sp.symbols('a1:4'); b = sp.symbols('b1:4'); c = sp.symbols('c1:4'); cb = sp.symbols('cb1:4')


def cls(x):
    return sp.expand(sp.prod([a[j] + b[j] + sp.conjugate(x[j]) * c[j] + x[j] * cb[j] for j in range(3)]))


def coeff_X(expr, eps):
    mono = sp.prod([c[j] if eps[j] == 1 else cb[j] for j in range(3)])
    return sp.Poly(expr, *a, *b, *c, *cb).coeff_monomial(mono)


EPS = list(itertools.product([1, -1], repeat=3))
ok6 = True
for x in itertools.product(MU4, repeat=3):
    sigma = x[0] * x[1] * x[2]
    cx = [sp.expand(t ** 2) for t in x]
    Zx = cls(x)
    for eps in EPS:
        want = sigma * sp.prod([cx[j] for j in range(3) if eps[j] == 1])
        ok6 &= sp.simplify(coeff_X(Zx, eps) - want) == 0
check("coefficient of X_eps in [Z_x] is sigma(x) prod_{eps_j = 1} c(x)_j, all 64 x and 8 eps", ok6)

# ---------------------------------------------------------------- check 7: Fourier inversion on the four orbits, and the signed sum of the thirty-two
ok7 = True
nu = {x: sp.Rational(random.randint(-5, 5), random.randint(1, 3)) for x in itertools.product(MU4, repeat=3)}
total = sp.expand(sum(nu[x] * cls(x) for x in nu))
F = {eps: coeff_X(total, eps) for eps in EPS}
for cvec in EPS:
    W = sum(nu[x] * x[0] * x[1] * x[2] for x in nu if tuple(sp.expand(t ** 2) for t in x) == tuple(sp.Integer(e) for e in cvec))
    inv = sp.Rational(1, 8) * sum(F[eps] * sp.prod([sp.Integer(cvec[j]) for j in range(3) if eps[j] == 1]) for eps in EPS)
    ok7 &= sp.simplify(W - inv) == 0
signed = sp.expand(sum((x[0] * x[1] * x[2]) * cls(x) for x in itertools.product(MU4, repeat=3) if (x[0] * x[1] * x[2]) ** 2 == 1))
Fs = {eps: coeff_X(signed, eps) for eps in EPS}
ok7 &= Fs[(1, 1, 1)] == 32 and Fs[(-1, -1, -1)] == 32 and all(Fs[e] == 0 for e in EPS if e not in [(1, 1, 1), (-1, -1, -1)])
check("W_c = (1/8) sum_eps F(eps) chi_eps(c) for random nu; the signed sum of the thirty-two has X-coefficients 32 at +-(1,1,1) and 0 elsewhere (N p = 32, W_c = 8)", ok7)

# ---------------------------------------------------------------- checks 8, 9: the exterior algebra of A_0, theta_h X_eps = 0 and the weights
# generators 0..5: dz_1..dz_6; 6..11: dzbar_1..dzbar_6
def weight(g):
    m = g % 6
    s = 1 if g < 6 else -1            # dz has +, dzbar has -
    e = [0, 0, 0]
    if m < 3:
        e[m] = s
    else:
        e[m - 3] = -s                  # dz_{3+j} weight -e_j, dzbar_{3+j} weight +e_j
    return tuple(e)


def wedge(m1, m2):
    """product of two monomials given as sorted tuples; returns (sign, monomial) or None"""
    if set(m1) & set(m2):
        return None
    seq = list(m1) + list(m2)
    sign = 1
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            if seq[i] > seq[j]:
                sign = -sign
    return sign, tuple(sorted(seq))


def X_mono(eps):
    gens = []
    for j in range(3):
        gens += [j, 6 + 3 + j] if eps[j] == 1 else [6 + j, 3 + j]       # c_j ~ dz_j dzbar_{3+j}, cbar_j ~ dzbar_j dz_{3+j}
    return tuple(sorted(gens))


ok8 = True
for eps in EPS:
    X = X_mono(eps)
    for m in range(6):                                                  # theta_h = sum h_m dz_m dzbar_m
        ok8 &= wedge((m, 6 + m), X) is None
    ok8 &= tuple(sum(weight(g)[j] for g in X) for j in range(3)) == tuple(2 * e for e in eps)
check("theta_h X_eps = 0 term by term, and X_eps has weight 2 eps", ok8)

ok9 = True
w4 = [tuple(sum(weight(g)[j] for g in mono) for j in range(3)) for mono in itertools.combinations(range(12), 4)]
ok9 &= all(w not in w4 and tuple(-t for t in w) not in w4 for w in [tuple(2 * e for e in eps) for eps in EPS])
for eps in EPS:
    target = tuple(2 * e for e in eps)
    monos = [mono for mono in itertools.combinations(range(12), 6) if tuple(sum(weight(g)[j] for g in mono) for j in range(3)) == target]
    ok9 &= monos == [X_mono(eps)]
check("H^4(A_0) has no class of weight +-2 eps, and X_eps spans the weight 2 eps part of H^6(A_0)", ok9)

# ---------------------------------------------------------------- checks 10-16: the line of four threefolds (Lemma VI.32) and the sixty-four (Theorem VI.33)
# check 10: at Y = E_jk the vector v gives dn_a(v) = a dzbar_k, dn_k(v) = (h_{3+j}/h_k) dzbar_{3+j}, dn_l(v) = 0
hs = sp.symbols('h1:7', positive=True)
ok10 = True
for j in range(3):
    for k in range(3):
        if k == j:
            continue
        l = 3 - j - k
        Y = [[sp.Integer(0)] * 3 for _ in range(3)]
        Y[j][k] = sp.Integer(1)
        v = tdh_vector(Y, hs)
        for xi_k in MU4:
            for xi_l in MU4:
                for aa in MU4:
                    dn_a = [v[j][bb] + aa * v[3 + j][bb] for bb in range(6)]          # coefficients of dzbar_b in dn_a(v)
                    dn_k = [v[k][bb] + xi_k * v[3 + k][bb] for bb in range(6)]
                    dn_l = [v[l][bb] + xi_l * v[3 + l][bb] for bb in range(6)]
                    ok10 &= all(sp.simplify(dn_a[bb] - (aa if bb == k else 0)) == 0 for bb in range(6))
                    ok10 &= all(sp.simplify(dn_k[bb] - (hs[3 + j] / hs[k] if bb == 3 + j else 0)) == 0 for bb in range(6))
                    ok10 &= all(dn_l[bb] == 0 for bb in range(6))
check("at Y = E_jk: dn_a(v) = a dzbar_k, dn_k(v) = (h_{3+j}/h_k) dzbar_{3+j}, dn_l(v) = 0, for all j != k, a, xi_k, xi_l", ok10)

# check 11: [C_a] wedge dzbar_{3+j} = (i/2)(dz_j + a dz_{3+j}) dzbar_j dzbar_{3+j}, and the two relations
# forms on B_j in the generators 0: dz_j, 1: dz_{3+j}, 2: dzbar_j, 3: dzbar_{3+j}, as dicts monomial -> coefficient
def wmul(f, g):
    out = {}
    for m1, c1 in f.items():
        for m2, c2 in g.items():
            r = wedge(m1, m2)
            if r is None:
                continue
            sgn, m = r
            out[m] = sp.expand(out.get(m, 0) + sgn * c1 * c2)
    return {m: c for m, c in out.items() if c != 0}


def curve_class(aa):
    one = {(0,): sp.Integer(1), (1,): aa}                       # dn_a = dz_j + a dz_{3+j}
    two = {(2,): sp.Integer(1), (3,): sp.conjugate(aa)}        # dnbar_a
    return {m: I / 2 * c for m, c in wmul(one, two).items()}


mu = {aa: sp.Symbol('mu_%d' % n) for n, aa in enumerate(MU4)}
dzbar3j = {(3,): sp.Integer(1)}
ok11 = True
total = {}
for aa in MU4:
    w = wmul(curve_class(aa), dzbar3j)
    ok11 &= w == {(0, 2, 3): I / 2, (1, 2, 3): sp.expand(I / 2 * aa)}
    for mono, cf in w.items():
        total[mono] = sp.expand(total.get(mono, 0) + mu[aa] * cf)
rel1 = sp.expand(total[(0, 2, 3)] * 2 / I)
rel2 = sp.expand(total[(1, 2, 3)] * 2 / I)
ok11 &= sp.expand(rel1 - sum(mu[aa] for aa in MU4)) == 0 and sp.expand(rel2 - sum(aa * mu[aa] for aa in MU4)) == 0
check("[C_a] dzbar_{3+j} = (i/2)(dz_j + a dz_{3+j}) dzbar_j dzbar_{3+j}; the coefficients of sum mu_a [C_a] dzbar_{3+j} are sum mu_a and sum a mu_a", ok11)

# check 12: the rational solutions of the two relations are mu_a = m a^2
rsyms = [sp.Symbol('r_%d' % n, real=True) for n in range(4)]
rel2r = rel2.subs({mu[aa]: rsyms[n] for n, aa in enumerate(MU4)})
eqs = [sum(rsyms), sp.re(sp.expand(rel2r)), sp.im(sp.expand(rel2r))]
sol = sp.linsolve(eqs, rsyms)
(vec,) = list(sol)
free12 = set().union(*[term.free_symbols for term in vec])
ok12 = len(free12) == 1 and vec[0] != 0
ok12 = ok12 and [sp.simplify(vec[n] / vec[0]) for n in range(4)] == [sp.expand(aa ** 2) for aa in MU4]
check("the relations sum mu_a = 0, sum a mu_a = 0 have the one-dimensional solution space mu_a = m a^2, i.e. mu_1 = mu_-1 = -mu_i = -mu_-i", ok12)

# check 13: Q . C_b = 8, Q^2 = 32, and C_1 meets C_i in |1 - i|^2 = 2 points: Q has finite stabiliser
QUARTER = [sp.Rational(p, 4) + sp.Rational(q, 4) * I for p in range(4) for q in range(4)]      # (1/4)Z[i] / Z[i]
ok13 = True
for bb in MU4:
    ok13 &= sum(sp.expand(abs(aa - bb) ** 2) for aa in MU4 if aa != bb) == 8
ok13 &= sum(sp.expand(abs(aa - bb) ** 2) for aa in MU4 for bb in MU4 if aa != bb) == 32
for aa in MU4:
    for bb in MU4:
        if aa != bb:
            pts = [u for u in QUARTER if in_lattice((aa - bb) * u)]       # u = z_j on C_a cap C_b, with z_{3+j} = -conj(a) u
            ok13 &= len(pts) == sp.expand(abs(aa - bb) ** 2)
ok13 &= len([u for u in QUARTER if in_lattice((1 - I) * u)]) == 2
check("Q . C_b = 8 for every b, Q^2 = 32, and C_a meets C_b in |a - b|^2 points, 2 for (1, i): Q is ample with finite stabiliser", ok13)

# check 14: the threefolds meeting Q x {y} for general y in Pi = C_{xi_k} x C_{xi_l} are the four T_a
tgen = sp.sqrt(2) / 7
ok14 = True
for j in range(3):
    for k in range(3):
        if k == j:
            continue
        l = 3 - j - k
        for xi_k in MU4:
            for xi_l in MU4:
                yk = (tgen, -sp.conjugate(xi_k) * tgen)           # a point of C_{xi_k} off the other curves
                yl = (sp.sqrt(3) / 11, -sp.conjugate(xi_l) * sp.sqrt(3) / 11)
                meeting = []
                for x in itertools.product(MU4, repeat=3):
                    ink = in_lattice(yk[0] + x[k] * yk[1])
                    inl = in_lattice(yl[0] + x[l] * yl[1])
                    if ink and inl:                                  # C_{x_j} meets Q always
                        meeting.append(x)
                ok14 &= sorted(meeting, key=str) == sorted([x for x in itertools.product(MU4, repeat=3) if x[k] == xi_k and x[l] == xi_l], key=str)
                ok14 &= len(meeting) == 4 and len({x[0] * x[1] * x[2] for x in meeting if (x[0] * x[1] * x[2]) ** 2 == 1}) == 2
check("the threefolds meeting Q x {y}, y general in Pi, are the four T_a, two of each family, for all j, k, xi_k, xi_l", ok14)

# check 15: mu_x / x_j^2 independent of x_j for each j forces mu_x = m sigma(x)^2
XS = list(itertools.product(MU4, repeat=3))
msym = {x: sp.Symbol('m_%d' % n) for n, x in enumerate(XS)}
eqs15 = []
for x in XS:
    for j in range(3):
        for aa in MU4:
            if aa != x[j]:
                xp = tuple(aa if jj == j else x[jj] for jj in range(3))
                eqs15.append(sp.expand(msym[x] * x[j] ** 2 - msym[xp] * xp[j] ** 2))      # x_j^{-2} = x_j^2
M15 = sp.Matrix([[sp.Poly(e, *[msym[x] for x in XS]).coeff_monomial(msym[x]) for x in XS] for e in eqs15])
ns = M15.nullspace()
ok15 = len(ns) == 1
if ok15:
    vec15 = ns[0]
    ref = vec15[XS.index((sp.Integer(1), sp.Integer(1), sp.Integer(1)))]
    ok15 &= all(sp.simplify(vec15[n] / ref - sp.expand((x[0] * x[1] * x[2]) ** 2)) == 0 for n, x in enumerate(XS))
check("the relations along all lines of four threefolds have the one-dimensional solution space mu_x = m sigma(x)^2", ok15)

# check 16: sum_x sigma(x)^2 [Z_x] = prod_j T_{2,j} = 0 in H^6(A_0), T_{2,j} = sum_a a^2 [C_a] = 0 in H^2(B_j)
ok16 = sp.expand(sum(sp.expand((x[0] * x[1] * x[2]) ** 2) * cls(x) for x in XS)) == 0
for j in range(3):
    ok16 &= sp.expand(sum(sp.expand(aa ** 2) * (a[j] + b[j] + sp.conjugate(aa) * c[j] + aa * cb[j]) for aa in MU4)) == 0
ok16 &= sp.expand(sum(cls(x) for x in XS if (x[0] * x[1] * x[2]) ** 2 == 1) - sum(cls(x) for x in XS if (x[0] * x[1] * x[2]) ** 2 == -1)) == 0
check("sum_x sigma(x)^2 [Z_x] = 0: T_{2,j} = 0 for each j, and the sum over the family sigma = +-1 equals the sum over sigma = +-i", ok16)

bad = [n for n, ok in checks if not ok]
print(f"threefold_supports: {len(checks) - len(bad)} checks passed, {len(bad)} failed")
sys.exit(1 if bad else 0)
