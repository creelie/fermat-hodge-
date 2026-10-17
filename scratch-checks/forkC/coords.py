# Print each configuration of an L file in the coordinates of sec14-composite:
# x <-> (a, b), a in Z/D, b in U = (Z/e')^x, x/N = a/D + b/e' (mod 1).
# At D = 6 the kinds are E (a=0), Y (a=3), Z+ (a=2), Z- (a=4), X+ (a=1), X- (a=5).
import sys, math
e = int(sys.argv[1]); v = int(sys.argv[2]); w = int(sys.argv[3]); fn = sys.argv[4]
D = 2**v * 3**w; N = D * e
kind6 = {0: 'E', 3: 'Y', 2: 'Z+', 4: 'Z-', 1: 'X+', 5: 'X-'}
for line in open(fn):
    t = line.split()
    if not t or t[0] != 'C': continue
    B = [int(s.split('/')[0]) for s in t[5:]]
    out = []
    for x in B:
        a = x * pow(e % D, -1, D) % D if D > 1 else 0
        b = x * pow(D % e, -1, e) % e
        k = kind6.get(a, str(a)) if D == 6 else str(a)
        out.append('%s_%d' % (k, b))
    print(' '.join(t[1:4]), '|', ' '.join(out))
