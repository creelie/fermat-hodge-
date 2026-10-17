/* Balanced sextuples at level m that generate Z/m, contain no pair, and have
   no direct or lowering move (odd primes l and l = 2), up to units.
   usage: sext m [verbose] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int m, units[4000], nu, half[4000], nh;
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int cmp(const void *x, const void *y) { return *(int *)x - *(int *)y; }
static int ord(int a) { return m / gcd(a, m); }

static int balanced(const int *a, int n) {
  for (int i = 0; i < nh; i++) {
    int t = half[i], s = 0;
    for (int k = 0; k < n; k++) s += (t * a[k]) % m;
    if (2 * s != n * m) return 0;
  }
  return 1;
}

/* profile: orders sorted nonincreasing; compare lexicographically */
static void profile(const int *a, int n, int *p) {
  for (int k = 0; k < n; k++) p[k] = ord(a[k]);
  qsort(p, n, sizeof(int), cmp);
  for (int k = 0; k < n / 2; k++) { int t = p[k]; p[k] = p[n - 1 - k]; p[n - 1 - k] = t; }
}
static int pless(const int *p, const int *q, int n) {
  for (int k = 0; k < n; k++) { if (p[k] < q[k]) return 1; if (p[k] > q[k]) return 0; }
  return 0;
}

static int primes[20], np;

/* returns 1 if A has a direct or lowering move */
static int hasmove(const int *a, int verbose) {
  int pa[6]; profile(a, 6, pa);
  for (int pi = 0; pi < np; pi++) {
    int l = primes[pi];
    for (int i = 0; i < 6; i++) {
      int x = a[i];
      if ((l * x) % m == 0) continue;
      /* Phi_l(x) */
      int phi[64], used[6] = {0}, k = 0, nb = 0, b[80];
      for (int j = 0; j < l; j++) phi[j] = (x + j * (m / l)) % m;
      int inS[64] = {0};
      for (int j = 0; j < l; j++)
        for (int r = 0; r < 6; r++)
          if (!used[r] && a[r] == phi[j]) { used[r] = 1; inS[j] = 1; k++; break; }
      for (int r = 0; r < 6; r++) if (!used[r]) b[nb++] = a[r];
      for (int j = 0; j < l; j++) if (!inS[j]) b[nb++] = (m - phi[j]) % m;
      b[nb++] = (l * x) % m;
      if (l == 2) b[nb++] = m / 2;
      if (nb <= 4) { if (verbose) printf("  direct l=%d x=%d\n", l, x); return 1; }
      if (nb == 6) {
        int pb[6]; profile(b, 6, pb);
        if (pless(pb, pa, 6)) { if (verbose) printf("  lower l=%d x=%d\n", l, x); return 1; }
      }
    }
  }
  return 0;
}

int main(int argc, char **argv) {
  m = atoi(argv[1]);
  int verbose = argc > 2;
  for (int t = 1; t < m; t++) if (gcd(t, m) == 1) { units[nu++] = t; if (2 * t < m) half[nh++] = t; }
  int r = m; np = 0;
  for (int p = 2; p <= r; p++) if (r % p == 0) { primes[np++] = p; while (r % p == 0) r /= p; }
  long found = 0, total = 0;
  int a[6];
  for (a[0] = 1; a[0] < m; a[0]++)
  for (a[1] = a[0]; a[1] < m; a[1]++)
  for (a[2] = a[1]; a[2] < m; a[2]++)
  for (a[3] = a[2]; a[3] < m; a[3]++) {
    int s = a[0] + a[1] + a[2] + a[3];
    int lo = 2 * m - s + 1; if (lo < a[3]) lo = a[3];
    int hi = (3 * m - s) / 2;
    for (a[4] = lo; a[4] <= hi; a[4]++) {
      a[5] = 3 * m - s - a[4];
      if (a[5] < a[4] || a[5] >= m) continue;
      if (!balanced(a, 6)) continue;
      /* canonical under units */
      int ok = 1;
      for (int i = 0; i < nu && ok; i++) {
        int b[6];
        for (int k = 0; k < 6; k++) b[k] = (units[i] * a[k]) % m;
        qsort(b, 6, sizeof(int), cmp);
        for (int k = 0; k < 6; k++) { if (b[k] < a[k]) { ok = 0; break; } if (b[k] > a[k]) break; }
      }
      if (!ok) continue;
      total++;
      /* pair-free */
      int pair = 0;
      for (int i = 0; i < 6 && !pair; i++)
        for (int j = i + 1; j < 6; j++) if ((a[i] + a[j]) % m == 0) { pair = 1; break; }
      if (pair) continue;
      int g = m;
      for (int k = 0; k < 6; k++) g = gcd(g, a[k]);
      if (g != 1) continue;
      if (hasmove(a, 0)) continue;
      found++;
      printf("m=%d IRR %d %d %d %d %d %d  orders", m, a[0], a[1], a[2], a[3], a[4], a[5]);
      for (int k = 0; k < 6; k++) printf(" %d", ord(a[k]));
      printf("\n");
    }
  }
  fprintf(stderr, "m=%d orbits=%ld irreducible=%ld\n", m, total, found);
  return 0;
}
