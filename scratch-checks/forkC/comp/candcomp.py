# Composite candidate exceptional e' (every prime factor >= LO): composite
# divisors e' of the numbers 2^a 3^b - 1, 2^a 3^b + 1, |2^a - 3^b|, 2^a + 3^b
# (0 <= a <= A, 0 <= b <= B, (a, b) != (0, 0)) all of whose prime factors are
# >= LO.  These are the e' with 2^a 3^b = +-1 mod e' for some (a, b) != 0,
# |a| <= A, |b| <= B.  usage: candcomp.py A B [LO]  (prints one e' per line)
import sys
def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
PR = primes_upto(400000)
def factorint(n):
    f = {}
    for p in PR:
        if p * p > n: break
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
    if n > 1: f[n] = f.get(n, 0) + 1   # n < 400000^2, so n is prime
    return f
A = int(sys.argv[1]); B = int(sys.argv[2]); LO = int(sys.argv[3]) if len(sys.argv) > 3 else 29
S = set()
for a in range(A + 1):
    for b in range(B + 1):
        if a == 0 and b == 0: continue
        for n in (2**a * 3**b - 1, 2**a * 3**b + 1, abs(2**a - 3**b), 2**a + 3**b):
            if n <= 1: continue
            f = {p: k for p, k in factorint(n).items() if p >= LO}
            divs = [1]
            for p, k in f.items():
                divs = [d * p**i for d in divs for i in range(k + 1)]
            for d in divs:
                g = factorint(d)
                if sum(g.values()) >= 2: S.add(d)
for e in sorted(S): print(e)
