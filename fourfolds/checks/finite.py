#!/usr/bin/env python3
"""Independent re-check of the finite arithmetic certified in
lean/FermatFourfolds.lean (same claims, written from scratch in Python)."""
from collections import Counter
from math import gcd
import sys

fails = 0
count = 0


def check(name, cond):
    global fails, count
    count += 1
    if not cond:
        fails += 1
        print("FAIL", name)


def units(M):
    return [t for t in range(1, M) if gcd(t, M) == 1]


def balanced(M, A):
    if sum(A) % M or any(a % M == 0 for a in A):
        return False
    return all(2 * sum(t * a % M for a in A) == len(A) * M for t in units(M))


def order(M, y):
    return M // gcd(y, M)


def neg(M, y):
    return (-y) % M


def mul(M, t, A):
    return [t * a % M for a in A]


def mseq(M, A, B):
    return Counter(a % M for a in A) == Counter(b % M for b in B)


def nopair(M, A):
    return all((A[i] + A[j]) % M for i in range(len(A)) for j in range(i + 1, len(A)))


def remove_all(A, S):
    A = list(A)
    for s in S:
        A.remove(s)
    return A


def move(M, A, T, S):
    return remove_all(A, S) + [neg(M, y) for y in remove_all(T, S)]


def isprime(p):
    return p >= 2 and all(p % d for d in range(2, int(p ** 0.5) + 1))


def oddprimes(M):
    return [l for l in range(3, M + 1, 2) if isprime(l) and M % l == 0]


def phi(M, l, x):
    return [(x + j * (M // l)) % M for j in range(l)]


def sigma(M, l, x):
    return phi(M, l, x) + [neg(M, l * x)]


def tee(M, x):
    return [x % M, (x + M // 2) % M, neg(M, 2 * x), M // 2]


def gens(M):
    G = [[y, neg(M, y)] for y in range(1, M)]
    for l in oddprimes(M):
        G += [sigma(M, l, x) for x in range(M) if l * x % M]
    if M % 2 == 0:
        G += [tee(M, x) for x in range(M) if 2 * x % M]
    return G


def vanishes(M, nu):
    return all(sum(1 for y in A if nu(y)) % 2 == 0 for A in gens(M))


# Section 2
check("T(3) at 28", tee(28, 3) == [3, 17, 22, 14])
check("Phi_5(1) at 20", phi(20, 5, 1) == [1, 5, 9, 13, 17] and neg(20, 5) == 15)
A = [3, 5, 13, 17, 19, 27]
check("move example", balanced(28, A) and mseq(28, move(28, A, tee(28, 3), [3, 17]),
      [5, 6, 13, 14, 19, 27]) and balanced(28, [5, 6, 13, 14, 19, 27])
      and [order(28, y) for y in (3, 17, 6, 14)] == [28, 28, 14, 2])
for M in (21, 28, 33, 35, 39, 44, 52, 66, 78, 102, 110, 114):
    check("standard balanced %d" % M, all(balanced(M, G) for G in gens(M)))

# Section 4
O21, O33, O39 = [1, 4, 9, 15, 16, 18], [1, 4, 16, 22, 25, 31], [1, 7, 16, 22, 34, 37]
check("O21 residues", mseq(21, O21, [x for x in range(21) if x % 3 == 1 and x % 7 in (1, 2, 4)]
                       + [9, 15, 18]))
check("O33 residues", mseq(33, O33, [x for x in range(33) if x % 3 == 1 and x % 11 in
                                     (1, 3, 4, 5, 9)] + [22]))
check("O39 residues", mseq(39, O39, [x for x in range(39) if x % 3 == 1 and x % 13 in
                                     (1, 3, 9, 7, 8, 11)]))
for M, O, sq, reps in ((21, O21, (1, 2, 4), (1, 2)), (33, O33, (1, 3, 4, 5, 9), (1, 5)),
                       (39, O39, (1, 3, 9), (1, 2, 4, 8))):
    q = {21: 7, 33: 11, 39: 13}[M]
    check("invariance %d" % M, all(mseq(M, mul(M, t, O), O) for t in units(M)
                                   if t % 3 == 1 and t % q in sq))
    check("cosets %d" % M, all(any(mseq(M, mul(M, t, O), mul(M, s, O)) or
                                   mseq(M, mul(M, t, O), [neg(M, y) for y in mul(M, s, O)])
                                   for s in reps) for t in units(M)))
    check("balanced O%d" % M, balanced(M, O) and sum(O) == 3 * M)
check("tO lists", mul(21, 2, O21) == [2, 8, 18, 9, 11, 15] and mul(33, 5, O33) ==
      [5, 20, 14, 11, 26, 23] and mul(39, 2, O39) == [2, 14, 32, 5, 29, 35] and
      mul(39, 4, O39) == [4, 28, 25, 10, 19, 31] and mul(39, 8, O39) == [8, 17, 11, 20, 38, 23])
check("O21 identity", sigma(21, 3, 2) == [2, 9, 16, 15] and
      mseq(21, O21 + [2, 19], sigma(21, 3, 2) + [1, 4, 18, 19]) and balanced(21, [1, 4, 18, 19]))
a = mul(66, 2, O33)
check("O33 identity", a == [2, 8, 32, 44, 50, 62] and mseq(66, tee(66, 32), [2, 32, 33, 65]) and
      mseq(66, tee(66, 8), [8, 33, 41, 50]) and
      mseq(66, a + [1, 65, 25, 41, 33, 33], [1, 25, 44, 62] + tee(66, 32) + tee(66, 8)) and
      balanced(66, [1, 25, 44, 62]) and balanced(66, a))
a = mul(78, 2, O39)
check("O39 identity", a == [2, 14, 32, 44, 68, 74] and mseq(78, tee(78, 32), [14, 32, 39, 71]) and
      mseq(78, tee(78, 5), [5, 39, 44, 68]) and
      mseq(78, a + [5, 73, 7, 71, 39, 39], [2, 7, 73, 74] + tee(78, 32) + tee(78, 5)) and
      balanced(78, [2, 7, 73, 74]) and balanced(78, a))
check("subsets mod 7", [S for S in ([a, b, c] for a in range(1, 7) for b in range(a + 1, 7)
                                    for c in range(b + 1, 7)) if sum(S) % 7 == 0]
      == [[1, 2, 4], [3, 5, 6]])
C = [sorted(mul(13, 2 ** j, [1, 3, 9])) for j in range(4)]
check("cosets mod 13", C == [[1, 3, 9], [2, 5, 6], [4, 10, 12], [7, 8, 11]] and
      all(sorted(neg(13, y) for y in C[j]) == C[(j + 2) % 4] for j in range(4)))
check("residues mod 7, 11", {x * x % 7 for x in range(1, 7)} == {1, 2, 4} and
      sorted(3 ** j % 7 for j in range(6)) == [1, 2, 3, 4, 5, 6] and
      {3 ** j % 11 for j in range(5)} == {x * x % 11 for x in range(1, 11)})


# Section 5
def Q(M):
    out = []
    for q in range(2, M + 1):
        if M % q:
            continue
        a = 0
        while q % 2 ** (a + 1) == 0:
            a += 1
        o = q >> a
        ps = oddprimes(o)
        if a in (0, 2) and all(o % (l * l) for l in ps) and ((a == 2) + len(ps)) % 2 == 0:
            out.append(q)
    return out


check("Q sets", [Q(M) for M in (114, 102, 44, 52, 33, 35, 39, 110, 1680)] ==
      [[57], [51], [44], [52], [33], [35], [39], [55], [12, 15, 20, 21, 28, 35, 420]])
for M, l in ((114, 19), (102, 17), (44, 11), (52, 13)):
    check("nu_%d vanishes on S_%d" % (l, M), vanishes(M, lambda y, M=M, l=l: order(M, y) == l))
for M in (33, 35, 39):
    check("nu_R vanishes on S_%d" % M, vanishes(M, lambda y, M=M: y * y % M == 1))


# Section 6
def angle(m, t, a):
    s = sum(t * x % m for x in a)
    assert s % m == 0
    return s // m


def halfunits(m):
    return [t for t in units(m) if 2 * t < m]


PAIRS = [
    (114, [1, 25, 43, 57, 102], [39, 63, 68, 80, 92], 5, [1, 25, 39, 43, 57, 63, 68, 80, 92, 102],
     [2, 2, 2, 2, 3, 2, 2, 2, 3, 3, 2, 2, 3, 2, 2, 3, 3, 2],
     [3, 3, 3, 3, 2, 3, 3, 3, 2, 2, 3, 3, 2, 3, 3, 2, 2, 3], lambda y: order(114, y) == 19, [102]),
    (44, [1, 5, 8, 33, 41], [9, 37, 42], 4, [1, 5, 8, 9, 33, 37, 41, 42],
     [2, 2, 3, 2, 2, 2, 3, 3, 2, 3], [2, 2, 1, 2, 2, 2, 1, 1, 2, 1],
     lambda y: order(44, y) == 11, [8]),
    (52, [1, 5, 16, 37, 45], [29, 18, 42, 50, 17], 5, [1, 5, 16, 17, 18, 29, 37, 42, 45, 50],
     [2, 2, 2, 2, 3, 2, 3, 2, 3, 2, 2, 3], [3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2],
     lambda y: order(52, y) == 13, [16]),
    (102, [1, 7, 51, 60, 85], [91, 34, 26, 98, 57], 5, [1, 7, 26, 34, 51, 57, 60, 85, 91, 98],
     [2, 2, 2, 2, 3, 2, 2, 3, 2, 2, 2, 3, 2, 3, 2, 3],
     [3, 3, 3, 3, 2, 3, 3, 2, 3, 3, 3, 2, 3, 2, 3, 2], lambda y: order(102, y) == 17, [60]),
    (35, [1, 2, 16, 21, 30], [17, 22, 31], 4, [1, 2, 16, 17, 21, 22, 30, 31],
     [2, 2, 2, 2, 2, 3, 2, 2, 2, 3, 3, 3], [2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1],
     lambda y: y * y % 35 == 1, [1]),
]
for m, a1, a2, s, beta, v1, v2, nu, hit in PAIRS:
    ok = all(x % m for x in a1 + a2) and sum(a1) % m == 0 and sum(a2) % m == 0
    ok = ok and all(angle(m, t, a1) + angle(m, t, a2) == s for t in units(m))
    ok = ok and [angle(m, t, a1) for t in halfunits(m)] == v1
    ok = ok and [angle(m, t, a2) for t in halfunits(m)] == v2
    ok = ok and mseq(m, a1 + a2, beta) and balanced(m, beta) and nopair(m, beta)
    ok = ok and [y for y in beta if nu(y)] == hit
    check("character pair %d" % m, ok)
check("order-l elements", [y for y in range(114) if order(114, y) == 19] == list(range(6, 114, 6))
      and [y for y in range(44) if order(44, y) == 11] == list(range(4, 44, 4))
      and [y for y in range(52) if order(52, y) == 13] == list(range(4, 52, 4))
      and [y for y in range(102) if order(102, y) == 17] == list(range(6, 102, 6))
      and [y for y in range(35) if y * y % 35 == 1] == [1, 6, 29, 34])
check("8 alpha at 35", mul(35, 8, [1, 2, 16, 21, 30]) == [8, 16, 23, 28, 30] and
      mul(35, 8, [17, 22, 31]) == [31, 1, 3])

PATTERNS = [
    (114, mul(114, 13, [39, 63, 68, 80, 92]), [51, 21, 86, 14, 56], 3,
     [((0, 0, 1, 2, 0), 1), ((0, 0, 2, 0, 1), 1), ((1, 3, 0, 0, 0), 1), ((2, 0, 0, 1, 2), 1)],
     [114, 228, 114, 228]),
    (114, [1, 25, 43, 57, 102], [1, 25, 43, 57, 102], 24,
     [((3, 1, 2, 0, 0), 7), ((0, 1, 5, 0, 1), 2), ((0, 0, 0, 2, 0), 12), ((1, 5, 0, 0, 1), 3),
      ((0, 0, 0, 0, 19), 1)], [114, 342, 114, 228, 1938]),
    (44, [1, 5, 8, 33, 41], [1, 5, 8, 33, 41], 11,
     [((3, 0, 0, 0, 1), 1), ((0, 0, 11, 0, 0), 1), ((1, 1, 0, 0, 2), 5), ((1, 2, 0, 1, 0), 3),
      ((0, 0, 0, 4, 0), 2)], [44, 88, 88, 44, 132]),
    (52, [1, 5, 16, 37, 45], [1, 5, 16, 37, 45], 14,
     [((0, 0, 0, 3, 1), 4), ((0, 1, 1, 0, 3), 1), ((2, 1, 0, 0, 1), 7), ((0, 0, 13, 0, 0), 1),
      ((0, 3, 0, 1, 0), 2)], [156, 156, 52, 208, 52]),
    (52, mul(52, 9, [29, 18, 42, 50, 17]), [1, 6, 14, 34, 49], 5,
     [((0, 0, 5, 1, 0), 1), ((3, 0, 0, 0, 1), 1), ((2, 0, 0, 3, 0), 1), ((0, 3, 0, 1, 0), 1),
      ((0, 1, 0, 0, 2), 2)], [104, 52, 104, 52, 104]),
    (102, mul(102, 37, [91, 34, 26, 98, 57]), [1, 34, 44, 56, 69], 6,
     [((0, 0, 0, 3, 2), 1), ((0, 0, 3, 0, 4), 1), ((0, 3, 0, 0, 0), 2), ((2, 0, 1, 1, 0), 3)],
     [306, 408, 102, 102]),
    (102, mul(102, 5, [1, 7, 51, 60, 85]), [5, 35, 51, 96, 17], 18,
     [((0, 0, 0, 0, 6), 2), ((0, 0, 0, 17, 0), 1), ((0, 0, 2, 0, 0), 9), ((0, 6, 0, 1, 0), 1),
      ((3, 2, 0, 0, 1), 6)], [102, 1632, 102, 306, 102]),
    (35, [1, 2, 16, 21, 30], [1, 2, 16, 21, 30], 50,
     [((0, 0, 0, 5, 0), 10), ((1, 1, 2, 0, 0), 25), ((1, 2, 0, 0, 1), 10), ((3, 1, 0, 0, 1), 5),
      ((0, 0, 0, 0, 35), 1)], [105, 35, 35, 35, 1050]),
]
for m, a, stated, D, cols, w in PATTERNS:
    ok = a == stated and all(x % m for x in a) and sum(a) % m == 0
    ok = ok and all(sum(e[k] * d for e, d in cols) == D for k in range(5))
    ok = ok and all(max(e) > 0 and min(e) == 0 and d > 0 for e, d in cols)
    ww = [sum(x * y for x, y in zip(e, a)) for e, d in cols]
    ok = ok and ww == w and all(x % m == 0 for x in ww)
    ok = ok and sum(d for e, d in cols) == D + 1
    check("block pattern %d %s" % (m, a), ok)
check("gcds", gcd(13, 114) == gcd(9, 52) == gcd(37, 102) == gcd(5, 102) == 1)
check("square roots 33 39", [y for y in range(33) if y * y % 33 == 1] == [1, 10, 23, 32] and
      [y for y in range(39) if y * y % 39 == 1] == [1, 14, 25, 38] and
      [y for y in O33 if y * y % 33 == 1] == [1] and [y for y in O39 if y * y % 39 == 1] == [1]
      and nopair(33, O33) and nopair(39, O39))

# Section 8
tr = lambda L, s: [(a, b, c) for a in L for b in L for c in L if a <= b <= c and a + b + c == s]
check("M=20", tr([5, 10, 15], 30) == [(5, 10, 15), (10, 10, 10)] and
      not nopair(20, [1, 17, 12, 5, 10, 15]) and not nopair(20, [1, 17, 12, 10, 10, 10]))
check("M=28 (b)", tr([7, 14, 21], 49) == [(7, 21, 21), (14, 14, 21)] and
      not nopair(28, [1, 9, 25, 7, 21, 21]) and not nopair(28, [1, 9, 25, 14, 14, 21]))
A = [1, 9, 16, 17, 20, 21]
A1 = move(28, A, tee(28, 1), [1])
A2 = move(28, A1, tee(28, 6), [20, 16, 14])
check("M=28 (c)", balanced(28, A) and mseq(28, A1, [2, 9, 13, 14, 16, 17, 20, 21]) and
      mseq(28, A2, [2, 9, 17, 13, 21, 22]) and (2 + 9 + 17) % 28 == 0 and (13 + 21 + 22) % 28 == 0)
check("M=44, 140", sum([1, 13, 37, 41, 5, 24]) == 121 and sum([7, 119, 84, 5, 45, 125]) == 385
      and sum([7, 119, 84, 55, 75, 115]) == 455)

# Section 10 (small local configurations)
for M, B in ((30, [1, 19, 25, 15]), (30, [1, 24, 20, 15]), (60, [1, 49, 40, 30]),
             (15, [1, 6, 13, 10]), (20, [1, 12, 17, 10]), (30, [1, 7, 27, 25]),
             (60, [2, 21, 57, 40]), (28, [1, 9, 25, 21]), (42, [1, 24, 38, 21]),
             (42, [1, 25, 37, 21]), (42, [1, 30, 32, 21]), (66, [1, 25, 62, 44]),
             (78, [1, 55, 61, 39])):
    check("small completion %d %s" % (M, B), balanced(M, B))

# Section 9 (level 110)
A110 = [19, 29, 39, 55, 79, 109]
nu = lambda y: y % 10 in (4, 5, 6)
check("level 110", balanced(110, A110) and nopair(110, A110) and vanishes(110, nu) and
      sum(map(nu, A110)) % 2 == 1 and oddprimes(110) == [5, 11] and
      sum(order(110, y) == 5 for y in A110) % 2 == 0 and
      sum(order(110, y) == 11 for y in A110) % 2 == 0 and tee(110, 1) == [1, 56, 108, 55] and
      [y for y in tee(110, 1) if y * y % 110 == 1] == [1])


# Section 1
def factor(M):
    f, d = {}, 2
    while d * d <= M:
        while M % d == 0:
            f[d] = f.get(d, 0) + 1
            M //= d
        d += 1
    if M > 1:
        f[M] = f.get(M, 0) + 1
    return f


def covered(M):
    f = factor(M)
    ps = set(f)
    return (M <= 100 or M % 2 == 1 or (M <= 250 and M not in (110, 114, 220, 228)) or
            len(ps) == 1 or (f.get(2) == 1 and len(ps) == 2) or
            (ps <= {2, 3, 5, 7} and M % 420) or ps <= {2, 3, 11} or ps <= {2, 3, 13} or
            ((ps <= {2, 3, 17} or ps <= {2, 3, 19}) and M % 4))


check("first open degrees", [M for M in range(1, 267) if M % 110 and not covered(M)]
      == [228, 258, 260, 266])

print("%d checks passed, %d failed" % (count - fails, fails))
sys.exit(1 if fails else 0)
