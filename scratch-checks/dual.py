"""Dual description: functionals w on F_2^{m-1} that vanish on Sbar, modulo
those vanishing also on Bbar.  Prints a low-weight representative of each
nonzero class as the set of residues where w = 1, grouped by order."""
import sys, itertools
from math import gcd
import numpy as np
sys.path.insert(0, "/dev/shm/hc")
from lat import Sbar, vec, standard
from inv import balanced_lattice


def nullspace_f2(rows, n):
    """Basis of {x in F_2^n : r.x = 0 for all rows r}."""
    R = [r.copy() for r in rows]
    piv = []
    M = np.array(R, dtype=np.uint8) if R else np.zeros((0, n), dtype=np.uint8)
    M = M % 2
    r = 0
    pivcols = []
    for c in range(n):
        p = None
        for i in range(r, M.shape[0]):
            if M[i, c]:
                p = i
                break
        if p is None:
            continue
        M[[r, p]] = M[[p, r]]
        for i in range(M.shape[0]):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        pivcols.append(c)
        r += 1
        if r == M.shape[0]:
            break
    free = [c for c in range(n) if c not in pivcols]
    basis = []
    for f in free:
        x = np.zeros(n, dtype=np.uint8)
        x[f] = 1
        for i, c in enumerate(pivcols):
            if M[i, f]:
                x[c] = 1
        basis.append(x)
    return basis


def main(m):
    n = m - 1
    srows = [vec([y, m - y], m) for y in range(1, m)] + [vec(s, m) for s in standard(m)]
    W = nullspace_f2(srows, n)
    B = balanced_lattice(m)
    brows = [vec([a for a in range(1, m) if c[a - 1] % 2], m) for c in B]
    # functionals in W vanishing on Bbar: solve within W
    Wm = np.array(W, dtype=np.uint8)
    # evaluate each W basis on each B row
    E = (Wm @ np.array(brows, dtype=np.uint8).T) % 2  # dimW x nB
    # kernel of E^T acting on coefficient vectors over W basis
    K = nullspace_f2([E[:, j] for j in range(E.shape[1])], len(W))
    print("m", m, "dim W", len(W), "dim W vanishing on B", len(K), "quotient", len(W) - len(K))
    return W, K, Wm


if __name__ == "__main__":
    main(int(sys.argv[1]))
