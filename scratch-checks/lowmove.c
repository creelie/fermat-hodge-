/* Lowering moves at an even level M prime to 3.  For every unit orbit of
   balanced sextuples that contain no pair, generate Z/M and are not a union
   of two zero-sum triples, decide
     tp  : A contains a T-pair {x, x+M/2}
     fb  : the move criterion of e84hc lem:movecrit holds for an odd prime
     gm  : some move (sigma_{l,x}, l odd, or T(x)) is good: after removing
           pairs the result has <= 4 elements, or it is a sextuple that does
           not generate, or is split, or has smaller profile.
   Prints "R a0..a5 tp fb gm" for the orbits with tp=fb=0, and a summary.
   usage: lowmove M */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int M, units[8000], nu, half[4000], nh, prm[20], np;
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int md(long a) { a %= M; if (a < 0) a += M; return (int)a; }
static int ord(int y) { return M / gcd(y, M); }
static int cmpd(const void *x, const void *y) { return *(int *)y - *(int *)x; }
static int depair(int *a, int n) {
  int used[64] = {0}, out[64], m = 0;
  for (int i = 0; i < n; i++) if (!used[i]) {
    int j; for (j = i + 1; j < n; j++) if (!used[j] && md(a[i] + a[j]) == 0) break;
    if (j < n) { used[i] = used[j] = 1; } }
  for (int i = 0; i < n; i++) if (!used[i]) out[m++] = a[i];
  memcpy(a, out, m * sizeof(int)); return m;
}
static int generates(const int *a, int n) { int g = M; for (int k = 0; k < n; k++) g = gcd(g, a[k]); return g == 1; }
static int split3(const int *a) {
  for (int i = 1; i < 6; i++) for (int j = i + 1; j < 6; j++) if (md((long)a[0] + a[i] + a[j]) == 0) return 1;
  return 0;
}
static void profile(const int *a, int *o) { for (int i = 0; i < 6; i++) o[i] = ord(a[i]); qsort(o, 6, sizeof(int), cmpd); }
static int lower(const int *b, const int *a) { int p[6], q[6]; profile(b, p); profile(a, q);
  for (int i = 0; i < 6; i++) { if (p[i] < q[i]) return 1; if (p[i] > q[i]) return 0; } return 0; }
static int good(int *b, int n, const int *a) {
  n = depair(b, n);
  if (n <= 4) return 1;
  if (n != 6) return 0;
  if (!generates(b, 6) || split3(b)) return 1;
  return lower(b, a);
}
static int gmove(const int *a) {
  for (int pi = 0; pi < np; pi++) { int l = prm[pi], d = M / l;
    for (int x = 0; x < d; x++) { if (md((long)l * x) == 0) continue;
      int rest[64], k = 0, b[64], n = 0, usedA[6] = {0};
      for (int j = 0; j < l; j++) { int y = x + j * d, f = -1;
        for (int i = 0; i < 6; i++) if (!usedA[i] && a[i] == y) { f = i; break; }
        if (f >= 0) { usedA[f] = 1; k++; } else rest[n++] = y; }
      if (k == 0) continue;
      int c = 0; for (int i = 0; i < 6; i++) if (!usedA[i]) b[c++] = a[i];
      for (int i = 0; i < n; i++) b[c++] = md(-rest[i]);
      if (l == 2) { b[c++] = md(2L * x); b[c++] = M / 2; } else b[c++] = md((long)l * x);
      if (c > 64) continue;
      if (good(b, c, a)) return 1;
    }
  }
  return 0;
}
static int tpair(const int *a) { int h = M / 2; for (int i = 0; i < 6; i++) for (int j = 0; j < 6; j++) if (i != j && md(a[i] + h) == a[j]) return 1; return 0; }
static int fbmove(const int *a) {
  for (int i = 0; i < 6; i++) { int x = a[i], e = ord(x);
    for (int pi = 0; pi < np; pi++) { int l = prm[pi]; if (l == 2 || e % l || e == l) continue;
      int d = M / l, cnt = 0;
      for (int j = 0; j < l; j++) { int y = md(x + (long)j * d); if (ord(y) != e) continue;
        for (int r = 0; r < 6; r++) if (a[r] == y) { cnt++; break; } }
      if (2 * cnt >= l + 1) return 1; } }
  return 0;
}
static int pre6(const int *a) { if (!generates(a, 6) || split3(a)) return 0; for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++) if (md(a[i] + a[j]) == 0) return 0; return 1; }
#include "enum6.h"
static long tot = 0, ntp = 0, nfb = 0, ngm = 0, nnone = 0, nbad = 0;
static void visit(const int *a) {
  tot++;
  int tp = tpair(a), fb = fbmove(a), gm = gmove(a);
  ntp += tp; nfb += (!tp && fb); ngm += gm;
  if (!tp && !fb) { nnone++; printf("R %d %d %d %d %d %d %d %d %d\n", a[0], a[1], a[2], a[3], a[4], a[5], tp, fb, gm); }
  else if (!gm) { printf("W %d %d %d %d %d %d %d %d %d\n", a[0], a[1], a[2], a[3], a[4], a[5], tp, fb, gm); }
  if (!gm) nbad++;
}
int main(int argc, char **argv) {
  M = atoi(argv[1]);
  for (int t = 1; t < M; t++) if (gcd(t, M) == 1) { units[nu++] = t; if (2 * t < M) half[nh++] = t; }
  { int r = M; for (int p = 2; p <= r; p++) if (r % p == 0) { prm[np++] = p; while (r % p == 0) r /= p; } }
  enum6(visit);
  printf("S M=%d orbits=%ld tpair=%ld fiber=%ld neither=%ld nogoodmove=%ld\n", M, tot, ntp, nfb, nnone, nbad);
  return 0;
}
