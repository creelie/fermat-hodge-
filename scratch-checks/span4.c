/* Over F_2: is every balanced sextuple at level M in the span of
   pairs, standard elements sigma_{p,x} (p | M prime, p = 2 adds M/2) and
   balanced quadruples?  Prints the unit-orbit representatives that are not.
   usage: span4 M */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define W 16
typedef struct { uint64_t w[W]; } vec;
static int M, half[2000], nh, units[4000], nu;
static vec basis[2048]; static int piv[2048], nb = 0, pivrow[4096];
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static void flip(vec *v, int a) { a %= M; if (a < 0) a += M; if (a) v->w[a >> 6] ^= 1ULL << (a & 63); }
static int lead(const vec *v) { for (int i = W - 1; i >= 0; i--) if (v->w[i]) return i * 64 + 63 - __builtin_clzll(v->w[i]); return -1; }
static int reduce(vec *v) { int l; while ((l = lead(v)) >= 0) { if (pivrow[l] < 0) return l; vec *b = &basis[pivrow[l]]; for (int i = 0; i < W; i++) v->w[i] ^= b->w[i]; } return -1; }
static int add(vec v) { int l = reduce(&v); if (l < 0) return 0; pivrow[l] = nb; basis[nb++] = v; return 1; }
static int balanced(const int *a, int n) {
  for (int i = 0; i < nh; i++) { long s = 0; int t = half[i]; for (int k = 0; k < n; k++) s += (long)(t * a[k]) % M; if (2 * s != (long)n * M) return 0; }
  return 1;
}
static int cmp(const void *x, const void *y) { return *(int *)x - *(int *)y; }
int main(int argc, char **argv) {
  M = atoi(argv[1]);
  memset(pivrow, -1, sizeof pivrow);
  for (int t = 1; t < M; t++) if (gcd(t, M) == 1) { units[nu++] = t; if (2 * t < M) half[nh++] = t; }
  for (int y = 1; y < M; y++) { vec v = {0}; flip(&v, y); flip(&v, M - y); add(v); }
  int r = M;
  for (int p = 2; p <= r; p++) if (r % p == 0) {
    while (r % p == 0) r /= p;
    for (int x = 0; x < M; x++) { if ((long)p * x % M == 0) continue;
      vec v = {0}; for (int j = 0; j < p; j++) flip(&v, x + j * (M / p)); flip(&v, -p * x); if (p == 2) flip(&v, M / 2); add(v); }
  }
  int ns = nb;
  int a[6];
  for (a[0] = 1; a[0] < M; a[0]++) for (a[1] = a[0]; a[1] < M; a[1]++) for (a[2] = a[1]; a[2] < M; a[2]++) {
    a[3] = (3 * M - a[0] - a[1] - a[2]) % M; if (a[3] == 0 || a[3] < a[2]) continue;
    if (a[0] + a[1] + a[2] + a[3] != 2 * M) continue;
    if (!balanced(a, 4)) continue;
    vec v = {0}; for (int k = 0; k < 4; k++) flip(&v, a[k]); add(v);
  }
  int nq = nb - ns;
  long tot = 0, bad = 0;
  for (a[0] = 1; a[0] < M; a[0]++) for (a[1] = a[0]; a[1] < M; a[1]++) for (a[2] = a[1]; a[2] < M; a[2]++) for (a[3] = a[2]; a[3] < M; a[3]++) {
    int s = a[0] + a[1] + a[2] + a[3]; int lo = 2 * M - s + 1; if (lo < a[3]) lo = a[3]; int hi = (3 * M - s) / 2;
    for (a[4] = lo; a[4] <= hi; a[4]++) { a[5] = 3 * M - s - a[4]; if (a[5] < a[4] || a[5] >= M) continue;
      if (!balanced(a, 6)) continue;
      int ok = 1;
      for (int i = 0; i < nu && ok; i++) { int b[6]; for (int k = 0; k < 6; k++) b[k] = (units[i] * a[k]) % M; qsort(b, 6, sizeof(int), cmp);
        for (int k = 0; k < 6; k++) { if (b[k] < a[k]) { ok = 0; break; } if (b[k] > a[k]) break; } }
      if (!ok) continue;
      tot++;
      vec v = {0}; for (int k = 0; k < 6; k++) flip(&v, a[k]);
      if (reduce(&v) >= 0) { bad++; printf("M=%d OUT %d %d %d %d %d %d\n", M, a[0], a[1], a[2], a[3], a[4], a[5]); }
    }
  }
  fprintf(stderr, "M=%d dimS=%d +quad=%d sextorbits=%ld outside=%ld\n", M, ns, nq, tot, bad);
  return 0;
}
