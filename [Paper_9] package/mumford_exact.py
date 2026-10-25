"""Exact checks in the split representation of SL(2)^3.

These are representation-theoretic checks, not algebraic-cycle constructions.
The model is over a splitting field, not rational coordinates on a Mumford fibre.
"""
from itertools import combinations, product
from collections import Counter
from fractions import Fraction
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
BITS = list(product((0, 1), repeat=3))


def wedge(a, b):
    if set(a) & set(b):
        return None, 0
    sign = (-1) ** sum(x > y for x in a for y in b)
    return tuple(sorted(a + b)), sign


def multiply(a, b):
    out = Counter()
    for i, x in a.items():
        for j, y in b.items():
            k, sign = wedge(i, j)
            if sign:
                out[k] += sign * x * y
    return {k: v for k, v in out.items() if v}


def rank(vectors):
    pivots = {}
    for vector in vectors:
        row = {i: Fraction(x) for i, x in enumerate(vector) if x}
        while row:
            i = min(row)
            if i not in pivots:
                a = row[i]
                pivots[i] = {j: x / a for j, x in row.items()}
                break
            a = row[i]
            for j, x in pivots[i].items():
                v = row.get(j, 0) - a * x
                if v:
                    row[j] = v
                else:
                    row.pop(j, None)
    return len(pivots)


def kernel(matrix, n):
    rows = [[Fraction(x) for x in row] for row in matrix if any(row)]
    pivots, k = [], 0
    for j in range(n):
        match = next((i for i in range(k, len(rows)) if rows[i][j]), None)
        if match is None:
            continue
        rows[k], rows[match] = rows[match], rows[k]
        a = rows[k][j]
        rows[k] = [x / a for x in rows[k]]
        for i in range(len(rows)):
            if i != k and rows[i][j]:
                a = rows[i][j]
                rows[i] = [x - a * y for x, y in zip(rows[i], rows[k])]
        pivots.append(j)
        k += 1
        if k == len(rows):
            break
    free = [j for j in range(n) if j not in pivots]
    basis = []
    for j in free:
        v = [Fraction(0)] * n
        v[j] = 1
        for i, p in enumerate(pivots):
            v[p] = -rows[i][j]
        basis.append(v)
    return basis


def bit_weight(b):
    return tuple(1 - 2 * x for x in b)


def invariant_character(weights, degree, semisimple=3):
    """Weyl-denominator extraction of trivial multiplicity, torus weight zero."""
    zero = (0,) * len(weights[0])
    dp = [Counter() for _ in range(degree + 1)]
    dp[0][zero] = 1
    for i, w in enumerate(weights):
        for d in range(min(degree, i + 1), 0, -1):
            for v, count in list(dp[d - 1].items()):
                dp[d][tuple(a + b for a, b in zip(v, w))] += count
    value = 0
    for choice in product((0, 1), repeat=semisimple):
        w = tuple(2 * c for c in choice) + (0,) * (len(zero) - semisimple)
        value += (-1) ** sum(choice) * dp[degree][w]
    return value


def main():
    weights = [bit_weight(BITS[i % 8]) for i in range(16)]
    basis = [b for b in combinations(range(16), 4)
             if all(sum(weights[i][j] for i in b) == 0 for j in range(3))]
    cols = {b: k for k, b in enumerate(basis)}
    rows = {}
    for j in range(3):
        for direction in (0, 1):
            for b, col in cols.items():
                for t, index in enumerate(b):
                    bits = BITS[index % 8]
                    if bits[j] == direction:
                        continue
                    target_bits = list(bits)
                    target_bits[j] = direction
                    target = 8 * (index // 8) + BITS.index(tuple(target_bits))
                    if target in b:
                        continue
                    new = b[:t] + (target,) + b[t + 1:]
                    sign = (-1) ** sum(new[a] > new[c]
                                          for a in range(4) for c in range(a + 1, 4))
                    key = (j, direction, tuple(sorted(new)))
                    rows.setdefault(key, [0] * len(basis))[col] += sign
    matrix = list(rows.values())
    inv = kernel(matrix, len(basis))
    assert all(sum(x * y for x, y in zip(row, v)) == 0
               for row in matrix for v in inv)
    theta = []
    for copy in (0, 1):
        theta.append({(8 * copy + i, 8 * copy + 7 - i): (-1) ** sum(BITS[i])
                      for i in range(4)})
    theta.append({(i, 8 + 7 - i): (-1) ** sum(BITS[i]) for i in range(8)})
    divisors = []
    for i in range(3):
        for j in range(i, 3):
            p = multiply(theta[i], theta[j])
            v = [p.get(b, 0) for b in basis]
            assert all(sum(x * y for x, y in zip(row, v)) == 0 for row in matrix)
            divisors.append(v)
    extra = []
    span = list(divisors)
    for v in inv:
        if rank(span + [v]) > rank(span):
            span.append(v)
            extra.append(v)
    assert len(inv) == 8 and rank(divisors) == 6 and len(extra) == 2
    wv = [bit_weight(b) for b in BITS]
    wz = []
    for i in range(3):
        for a, b in product((-1, 1), repeat=2):
            w = [0] * 6
            w[i], w[3 + i] = a, b
            wz.append(tuple(w))
    mixed = [w + (0, 0, 0) for w in wv * 2] + wz
    character_counts = {'V_square_degree4': invariant_character(wv * 2, 4),
                        'Z_degree2': invariant_character(wz, 2),
                        'X_X_Z_degree4': invariant_character(mixed, 4)}
    assert character_counts == {'V_square_degree4': 8, 'Z_degree2': 3,
                                'X_X_Z_degree4': 26}
    torus_counts = {'Z_degree2': invariant_character(wz, 2, semisimple=0),
                    'X_X_Z_degree4': invariant_character(mixed, 4, semisimple=0)}
    assert torus_counts['Z_degree2'] == 6
    assert torus_counts['X_X_Z_degree4'] > 26
    data = {'status': 'PASS', 'arithmetic': 'exact integers and rational fractions',
            'weight_zero_columns': len(basis), 'raising_lowering_rows': len(matrix),
            'Mumford_square_invariant_dimension': len(inv),
            'divisor_product_dimension': rank(divisors), 'exceptional_dimension': len(extra),
            'independent_character_counts': character_counts,
            'maximal_torus_invariant_counts': torus_counts,
            'split_model_only': True, 'algebraic_representatives_constructed': False,
            'F2_proved': False, 'F3prime_proved': False, 'Hodge_conjecture_proved': False,
            'model_exceptional_vectors': [
                [{'indices': list(b), 'coefficient': str(v[k])}
                 for k, b in enumerate(basis) if v[k]] for v in extra]}
    (ROOT / 'mumford-exact-results.json').write_text(json.dumps(data, indent=2) + '\n', encoding='utf8')
    print(json.dumps({k: v for k, v in data.items() if k != 'model_exceptional_vectors'}, indent=2))


if __name__ == '__main__':
    main()
