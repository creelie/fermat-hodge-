/* Move graph at level M.  For every unit orbit of balanced sextuples that
   contain no pair and generate Z/M, print
     R a0..a5 split
   followed by one line per move result:
     E D            result has <= 4 elements after removing pairs
     E N            result is a sextuple that does not generate Z/M
     E X b0..b5     result is a pair-free generating sextuple (canonical rep)
   split = 1 if the sextuple is a union of two zero-sum triples.
   Moves: sigma_{l,x} (odd prime l | M) and T(x) (2 | M).  usage: movesG M */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int M, units[8000], nu, half[4000], nh, prm[20], np;
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int md(long a) { a %= M; if (a < 0) a += M; return (int)a; }
static int cmpi(const void *x, const void *y) { return *(int *)x - *(int *)y; }
static int balanced(const int *a, int n) {
  long s0 = 0; for (int k = 0; k < n; k++) s0 += a[k]; if (s0 % M) return 0;
  for (int i = 0; i < nh; i++) { long s = 0; int t = half[i]; for (int k = 0; k < n; k++) s += (long)t * a[k] % M; if (2 * s != (long)n * M) return 0; }
  return 1;
}
static int depair(int *a, int n) {
  int used[64] = {0}, out[64], m = 0;
  for (int i = 0; i < n; i++) if (!used[i]) {
    int j; for (j = i + 1; j < n; j++) if (!used[j] && md(a[i] + a[j]) == 0) break;
    if (j < n) { used[i] = used[j] = 1; } }
  for (int i = 0; i < n; i++) if (!used[i]) out[m++] = a[i];
  memcpy(a, out, m * sizeof(int)); return m;
}
static int generates(const int *a, int n) { int g = M; for (int k = 0; k < n; k++) g = gcd(g, a[k]); return g == 1; }
static void canon(const int *a, int *c) {
  int best[6]; for (int i = 0; i < nu; i++) { int b[6]; for (int k = 0; k < 6; k++) b[k] = (int)((long)units[i] * a[k] % M); qsort(b, 6, sizeof(int), cmpi);
    if (i == 0 || memcmp(b, best, sizeof b) < 0) { int lt = 0; if (i) for (int k = 0; k < 6; k++) { if (b[k] < best[k]) { lt = 1; break; } if (b[k] > best[k]) break; } if (i == 0 || lt) memcpy(best, b, sizeof b); } }
  memcpy(c, best, sizeof best);
}
static int split3(const int *a) {
  for (int i = 1; i < 6; i++) for (int j = i + 1; j < 6; j++) if (md((long)a[0] + a[i] + a[j]) == 0) return 1;
  return 0;
}
static void emit(int *b, int n) {
  n = depair(b, n);
  if (n <= 4) { printf("E D\n"); return; }
  if (n == 6) { if (!generates(b, 6)) { printf("E N\n"); return; } int c[6]; canon(b, c); printf("E X %d %d %d %d %d %d\n", c[0], c[1], c[2], c[3], c[4], c[5]); return; }
  printf("E L %d\n", n);
}
static void moves(const int *a) {
  for (int pi = 0; pi < np; pi++) { int l = prm[pi], d = M / l;
    for (int x = 0; x < d; x++) { if (md((long)l * x) == 0) continue;
      int inA[64], k = 0, b[64], n = 0, usedA[6] = {0};
      for (int j = 0; j < l; j++) { int y = x + j * d; int f = -1;
        for (int i = 0; i < 6; i++) if (!usedA[i] && a[i] == y) { f = i; break; }
        if (f >= 0) { usedA[f] = 1; k++; } else inA[n++] = y; }
      if (k == 0) continue;
      int c = 0; for (int i = 0; i < 6; i++) if (!usedA[i]) b[c++] = a[i];
      for (int i = 0; i < n; i++) b[c++] = md(-inA[i]);
      if (l == 2) { b[c++] = md(2L * x); b[c++] = M / 2; } else b[c++] = md((long)l * x);
      emit(b, c);
    }
  }
}
int main(int argc, char **argv) {
  M = atoi(argv[1]);
  for (int t = 1; t < M; t++) if (gcd(t, M) == 1) { units[nu++] = t; if (2 * t < M) half[nh++] = t; }
  { int r = M; for (int p = 2; p <= r; p++) if (r % p == 0) { prm[np++] = p; while (r % p == 0) r /= p; } }
  int a[6]; long tot = 0;
  for (a[0] = 1; a[0] < M; a[0]++) for (a[1] = a[0]; a[1] < M; a[1]++) for (a[2] = a[1]; a[2] < M; a[2]++) for (a[3] = a[2]; a[3] < M; a[3]++) {
    int s = a[0] + a[1] + a[2] + a[3]; int lo = 2 * M - s + 1; if (lo < a[3]) lo = a[3]; int hi = (3 * M - s) / 2;
    for (a[4] = lo; a[4] <= hi; a[4]++) { a[5] = 3 * M - s - a[4]; if (a[5] < a[4] || a[5] >= M) continue;
      if (!generates(a, 6)) continue;
      { int pr = 0; for (int i = 0; i < 6 && !pr; i++) for (int j = i + 1; j < 6; j++) if (md(a[i] + a[j]) == 0) { pr = 1; break; } if (pr) continue; }
      if (!balanced(a, 6)) continue;
      int ok = 1;
      for (int i = 0; i < nu && ok; i++) { int b[6]; for (int k = 0; k < 6; k++) b[k] = (units[i] * a[k]) % M; qsort(b, 6, sizeof(int), cmpi);
        for (int k = 0; k < 6; k++) { if (b[k] < a[k]) { ok = 0; break; } if (b[k] > a[k]) break; } }
      if (!ok) continue;
      tot++;
      printf("R %d %d %d %d %d %d %d\n", a[0], a[1], a[2], a[3], a[4], a[5], split3(a));
      moves(a);
    }
  }
  fprintf(stderr, "M=%d orbits=%ld\n", M, tot);
  return 0;
}
