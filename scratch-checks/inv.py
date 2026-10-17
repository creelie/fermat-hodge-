"""Invariants of B_m / S_m mod 2.

B = balanced multisets (integer lattice), S = pairs + standard elements.
Computes Bbar = image of B in F_2^{m-1}, Sbar, and the quotient
(Bbar + Sbar)/Sbar, with a basis of functionals w (even, satisfying the
mod-2 distribution relations) that detect it.
"""
import sys
from math import gcd
sys.path.insert(0, "/dev/shm/hc")
from lat import Sbar, vec, standard


def int_kernel(rows, n):
    """Integer kernel basis of the matrix with given rows (list of lists of
    ints of length n), by unimodular column operations."""
    # columns: each column is (A-part, identity-part)
    cols = [[r[j] for r in rows] + [1 if i == j else 0 for i in range(n)]
            for j in range(n)]
    nr = len(rows)
    piv = 0
    for r in range(nr):
        # among columns piv.., make entries at row r zero except one
        while True:
            nz = [j for j in range(piv, n) if cols[j][r] != 0]
            if len(nz) <= 1:
                break
            j0 = min(nz, key=lambda j: abs(cols[j][r]))
            for j in nz:
                if j == j0:
                    continue
                q = cols[j][r] // cols[j0][r]
                cols[j] = [x - q * y for x, y in zip(cols[j], cols[j0])]
        nz = [j for j in range(piv, n) if cols[j][r] != 0]
        if nz:
            j = nz[0]
            cols[piv], cols[j] = cols[j], cols[piv]
            piv += 1
    return [c[nr:] for c in cols[piv:]]


def balanced_lattice(m):
    units = [t for t in range(1, m) if gcd(t, m) == 1 and 2 * t < m]
    n = m - 1  # index a-1 for a in 1..m-1
    rows = []
    for t in units:
        rows.append([2 * ((t * a) % m) - m for a in range(1, m)])
    K = int_kernel(rows, n)
    # impose sum condition: sum c_a a = 0 mod m. Kernel of K -> Z/m.
    s = [sum(c[a - 1] * a for a in range(1, m)) % m for c in K]
    # integer kernel of [s | m] on Z^{len K + 1}
    K2 = int_kernel([s + [m]], len(K) + 1)
    basis = []
    for v in K2:
        c = [0] * n
        for i, coef in enumerate(v[:-1]):
            if coef:
                for a in range(n):
                    c[a] += coef * K[i][a]
        basis.append(c)
    return basis


if __name__ == "__main__":
    m = int(sys.argv[1])
    B = balanced_lattice(m)
    S = Sbar(m)
    d0 = S.dim() if hasattr(S, "dim") else None
    from lat import F2Space
    extra = []
    for c in B:
        v = 0
        for a in range(1, m):
            if c[a - 1] % 2:
                v |= 1 << (a - 1)
        if not S.contains(v):
            S.add(v)
            extra.append(c)
    print("m", m, "rank B", len(B), "dim (B+S)/S over F2:", len(extra))
