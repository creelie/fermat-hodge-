/* hilbert.c -- Hilbert symbols and the rational invariants of Table II of
   the paper (Sect. V, the chain for sqrt 6).  Exact integer arithmetic.
   For a diagonal form <a_1,...,a_n> over Q: rank, signature, discriminant
   modulo squares and the Hasse invariant eps_p = prod_{i<j} (a_i,a_j)_p at
   p = 2, 3, 5 (and the product formula over all places as a self-test).
   Build: cc -O2 -o hilbert hilbert.c && ./hilbert */
#include <stdio.h>
#include <stdlib.h>
static long ipow_mod(long a, long e, long m) { long r = 1; a %= m; if (a < 0) a += m; while (e) { if (e & 1) r = r * a % m; a = a * a % m; e >>= 1; } return r; }
static int legendre(long a, long p) { a %= p; if (a < 0) a += p; if (a == 0) return 0; return ipow_mod(a, (p - 1) / 2, p) == 1 ? 1 : -1; }
static long sqfree(long a) { /* squarefree part, sign kept */
    long s = a < 0 ? -1 : 1, r = 1; a = labs(a);
    for (long p = 2; p * p <= a; p++) { int e = 0; while (a % p == 0) { a /= p; e++; } if (e & 1) r *= p; }
    return s * r * a;
}
static int hilbert(long a, long b, long p) { /* (a,b)_p, a, b nonzero */
    a = sqfree(a); b = sqfree(b);
    if (p == 0) return (a < 0 && b < 0) ? -1 : 1;              /* the real place */
    int al = 0, be = 0; long u = a, v = b;
    while (u % p == 0) { u /= p; al++; }
    while (v % p == 0) { v /= p; be++; }
    if (p != 2) { int s = ((al * be * ((p - 1) / 2)) & 1) ? -1 : 1; int lu = legendre(u, p), lv = legendre(v, p); for (int i = 0; i < be; i++) s *= lu; for (int i = 0; i < al; i++) s *= lv; return s; }
    long eu = ((u - 1) / 2) & 1, ev = ((v - 1) / 2) & 1, ou = ((u * u - 1) / 8) & 1, ov = ((v * v - 1) / 8) & 1;
    return ((eu * ev + al * ov + be * ou) & 1) ? -1 : 1;
}
struct Form { const char *name; int n; long a[16]; };
static void invariants(const struct Form *f, int *pos, int *neg, long *d, int eps[3]) {
    *pos = *neg = 0; *d = 1; const long P[3] = {2, 3, 5};
    for (int i = 0; i < f->n; i++) { if (f->a[i] > 0) (*pos)++; else (*neg)++; *d = sqfree(*d * f->a[i]); }
    for (int k = 0; k < 3; k++) { eps[k] = 1; for (int i = 0; i < f->n; i++) for (int j = i + 1; j < f->n; j++) eps[k] *= hilbert(f->a[i], f->a[j], P[k]); }
}
int main(void) {
    /* T = Tr_{E/Q} q_E diagonalised modulo squares; <1,-10>; T + <1,-10>;
       V3 = U^3 + A_2(-1)^2 with A_2(-1) = <-2,-6>; V2 = U^3 + E8(-2) = U^3 + <-2>^8. */
    struct Form forms[5] = {
        {"T", 8, {-1, -6, -1, -6, -1, 3, -2, 15}},
        {"<1,-10>", 2, {1, -10}},
        {"T+<1,-10>", 10, {-1, -6, -1, -6, -1, 3, -2, 15, 1, -10}},
        {"V3", 10, {1, -1, 1, -1, 1, -1, -2, -6, -2, -6}},
        {"V2", 14, {1, -1, 1, -1, 1, -1, -2, -2, -2, -2, -2, -2, -2, -2}}};
    /* Table II of the paper: rank, signature, d, eps_2, eps_3, eps_5 */
    const long table[5][6] = {{8, 2, 10, 1, -1, 1}, {2, 1, -10, 1, 1, 1}, {10, 3, -1, 1, -1, 1}, {10, 3, -1, 1, -1, 1}, {14, 3, -1, -1, 1, 1}};
    int ok = 1;
    for (int k = 0; k < 5; k++) {
        int pos, neg, eps[3]; long d; invariants(&forms[k], &pos, &neg, &d, eps);
        int row = (forms[k].n == table[k][0] && pos == table[k][1] && d == table[k][2] && eps[0] == table[k][3] && eps[1] == table[k][4] && eps[2] == table[k][5]);
        printf("%-10s rank %2d signature (%d,%d) d=%3ld eps_2=%2d eps_3=%2d eps_5=%2d  %s\n", forms[k].name, forms[k].n, pos, neg, d, eps[0], eps[1], eps[2], row ? "matches Table II" : "DIFFERS");
        ok &= row;
    }
    /* Hasse-Minkowski: T + <1,-10> and V3 have the same rank, signature, d and eps at every prime (checked at 2, 3, 5; at other primes every entry is a unit times a square so eps = +1). */
    int ok2 = 1; { int p1, n1, p2, n2, e1[3], e2[3]; long d1, d2; invariants(&forms[2], &p1, &n1, &d1, e1); invariants(&forms[3], &p2, &n2, &d2, e2);
        ok2 = (p1 == p2 && d1 == d2 && e1[0] == e2[0] && e1[1] == e2[1] && e1[2] == e2[2]); }
    printf("T + <1,-10> isometric to V3 over Q: %s\n", ok2 ? "yes" : "NO");
    /* product formula self-test */
    int ok3 = 1; const long P[4] = {2, 3, 5, 7};
    for (long a = -30; a <= 30; a++) for (long b = -30; b <= 30; b++) { if (!a || !b) continue; int pr = hilbert(a, b, 0); for (int k = 0; k < 4; k++) pr *= hilbert(a, b, P[k]);
        long x = labs(sqfree(a) * sqfree(b)); for (int k = 0; k < 4; k++) while (x % P[k] == 0) x /= P[k]; if (x == 1 && pr != 1) ok3 = 0; }
    printf("product formula on pairs with primes in {2,3,5,7}: %s\n", ok3 ? "holds" : "FAILS");
    ok = ok && ok2 && ok3;
    printf("hilbert.c: %s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}
