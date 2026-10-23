"""Exact split-representation check; no claim of algebraic cycle construction."""
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path

weights = list(product((-1, 1), repeat=3))

def exterior_weights(k):
    return Counter(tuple(sum(weights[j][t] for j in s) for t in range(3))
                   for s in combinations(range(8), k))

def tensor(a, b):
    out = Counter()
    for x, n in a.items():
        for y, m in b.items():
            out[tuple(x[i]+y[i] for i in range(3))] += n*m
    return out

def trivial_multiplicity(w):
    # Weyl character inversion for SL(2)^3.
    return sum((-1)**sum(s)*w[tuple(2*x for x in s)]
               for s in product((0, 1), repeat=3))

parts = [trivial_multiplicity(tensor(exterior_weights(k), exterior_weights(4-k)))
         for k in range(5)]
degree_two = sum(trivial_multiplicity(tensor(exterior_weights(k), exterior_weights(2-k)))
                 for k in range(3))

def wedge(a, b):
    out = Counter()
    for u, x in a.items():
        for v, y in b.items():
            if set(u).intersection(v):
                continue
            sign = (-1)**sum(i > j for i in u for j in v)
            out[tuple(sorted(u+v))] += sign*x*y
    return {k: v for k, v in out.items() if v}

def epsilon(a, b):
    if any(x == y for x, y in zip(a, b)):
        return 0
    return (-1)**sum(x == 1 for x in a)

d1, d2, cross = {}, {}, {}
for i in range(8):
    for j in range(8):
        e = epsilon(weights[i], weights[j])
        if not e:
            continue
        cross[(i, 8+j)] = e
        if i < j:
            d1[(i, j)] = e
            d2[(8+i, 8+j)] = e
divisors = [d1, d2, cross]
columns = [wedge(divisors[i], divisors[j]) for i in range(3) for j in range(i, 3)]
# Six columns: exact rank without external packages.
from fractions import Fraction
rows = [[Fraction(c.get(k, 0)) for c in columns]
        for k in sorted(set().union(*(set(c) for c in columns)))]
rank = 0
for col in range(6):
    pivot = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
    if pivot is None:
        continue
    rows[rank], rows[pivot] = rows[pivot], rows[rank]
    value = rows[rank][col]
    rows[rank] = [x/value for x in rows[rank]]
    for i in range(rank+1, len(rows)):
        value = rows[i][col]
        if value:
            rows[i] = [x-value*y for x, y in zip(rows[i], rows[rank])]
    rank += 1

result = dict(degree_two_invariants=degree_two,
              degree_four_kunneth_invariants=parts,
              degree_four_invariants=sum(parts), divisor_product_rank=rank,
              exceptional_quotient_dimension=sum(parts)-rank,
              scope="Split representation only; no algebraic representatives constructed")
assert degree_two == 3 and parts == [1, 1, 4, 1, 1] and rank == 6
Path(__file__).with_name('mumford-results.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result))
