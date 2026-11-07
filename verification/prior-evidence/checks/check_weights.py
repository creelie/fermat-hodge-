"""Exact checks of the weight counts and the two swap calculations."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product


def wedge_weights(weights, degree):
    return Counter(tuple(map(sum, zip(*subset)))
                   for subset in combinations(weights, degree))


def check_mumford_counts():
    weights = list(product((-1, 1), repeat=3))
    c3 = wedge_weights(weights, 3)
    c4 = wedge_weights(weights, 4)
    assert [c3[(3,) * j + (1,) * (3 - j)] for j in range(4)] == [4, 1, 0, 0]
    assert [c4[(2,) * j + (0,) * (3 - j)] for j in range(4)] == [8, 4, 2, 1]
    assert sum((-1)**sum(e) * c3[tuple(1 + 2*i for i in e)]
               for e in product((0, 1), repeat=3)) == 1
    assert sum((-1)**sum(e) * c4[tuple(2*i for i in e)]
               for e in product((0, 1), repeat=3)) == 1


def check_cm_weights():
    expected = Counter(product((-1, 1), repeat=3))
    expected[(1, 1, 1)] += 2
    expected[(-1, -1, -1)] += 2
    actual = Counter(tuple(left if j == i else right for j in range(3))
                     for i in range(3) for left, right in product((-1, 1), repeat=2))
    assert actual == expected
    tetrahedron = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
    for multiplicities in product(range(-4, 5), repeat=4):
        weighted_sum = tuple(sum(m*w[i] for m, w in zip(multiplicities, tetrahedron))
                             for i in range(3))
        assert (weighted_sum == (0, 0, 0)) == (len(set(multiplicities)) == 1)


def check_partial_transpose():
    def multiply(a, b):
        return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
                 for j in range(len(b[0]))] for i in range(len(a))]

    basis = list(product(range(2), repeat=2))
    identity = [[int(a == b) for b in basis] for a in basis]
    swap = [[int(a == b[::-1]) for b in basis] for a in basis]
    first_transpose = [[int((b[0], a[1]) == (b[1], a[0]))
                        for b in basis] for a in basis]
    j = ((0, 1), (-1, 0))
    j_left = [[j[a[0]][b[0]] * int(a[1] == b[1]) for b in basis] for a in basis]
    inverse = [[-entry for entry in row] for row in j_left]
    assert multiply(multiply(inverse, first_transpose), j_left) == [
        [u - v for u, v in zip(a, b)] for a, b in zip(identity, swap)]

    for si, sj, sk in product(map(Fraction, (-1, 1)), repeat=3):
        adjoint = (1 - si/2) * (sj/2) * (sk/2)
        primitive = (si/2) * (1 - sj/2) * (1 - sk/2)
        assert (64 * adjoint**2 - 1)/8 == (1-si)/2
        assert (primitive < 0) == (si < 0)


def check_adams_projector():
    for degree in range(15):
        value = Fraction(1)
        for j in range(15):
            if j != 2:
                value *= Fraction(2**degree - 2**j, 4 - 2**j)
        assert value == int(degree == 2)


def check_root_intertwiners():
    source = list(product((-1, 1), repeat=3))
    target = list(product(range(3), (-1, 1), (-1, 1)))
    weights = [tuple(left if j == i else right for j in range(3))
               for i, left, right in target]
    coefficients = [(a, b) for a, w in enumerate(weights)
                    for b, v in enumerate(source) if w == v]
    assert len(coefficients) == 12

    def equations(axis, before):
        rows = [[0] * len(coefficients) for _ in range(len(source)*len(target))]
        for c, (a, b) in enumerate(coefficients):
            i, left, right = target[a]
            if i == axis and left == before:
                new_a = target.index((i, -left, right))
                rows[new_a*len(source) + b][c] += 1
            if source[b][axis] == -before:
                new_weight = list(source[b])
                new_weight[axis] = before
                new_b = source.index(tuple(new_weight))
                rows[a*len(source) + new_b][c] -= 1
        return rows

    def rank(rows):
        pivots = {}
        for row in rows:
            row = list(map(Fraction, row))
            for pivot, basis in pivots.items():
                scale = row[pivot]
                row = [a - scale*b for a, b in zip(row, basis)]
            pivot = next((j for j, a in enumerate(row) if a), None)
            if pivot is not None:
                scale = row[pivot]
                pivots[pivot] = [a / scale for a in row]
        return len(pivots)

    assert rank(equations(2, 1)) == 6
    all_roots = [row for axis in range(3) for sign in (-1, 1)
                 for row in equations(axis, sign)]
    assert rank(all_roots) == 12


if __name__ == "__main__":
    check_mumford_counts()
    print("PASS: Mumford exterior-weight multiplicities")
    check_cm_weights()
    print("PASS: matched CM weights and tetrahedron relation")
    check_partial_transpose()
    print("PASS: partial symplectic transpose and swap recovery")
    check_adams_projector()
    print("PASS: Adams projector in all fifteen cohomological degrees")
    check_root_intertwiners()
    print("PASS: rank six at one root and rank twelve for all roots")
