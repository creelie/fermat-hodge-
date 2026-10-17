/* Full move search at an even level M.  For every unit orbit of balanced
   sextuples that contain no pair, generate Z/M and are not a union of two
   zero-sum triples, search for a chain of at most DEPTH moves by standard
   multisets (sigma_{l,x}, l odd, and T(x) = {x, x+M/2, -2x, M/2}), each
   move B -> (B - S) + (-(sigma - S)) with S = sigma meet B (one copy each),
   pairs removed after each move, sizes capped at CAP.  Success: at most
   four elements, or a sextuple that does not generate, is split, contains
   a pair, or has smaller profile than the starting sextuple.
   Prints "R a0..a5" for the orbits with no success.
   usage: fullmove M [DEPTH] [CAP] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int M, units[8000], nu, half[4000], nh, prm[20], np, DEPTH = 4, CAP = 12;
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int md(long a) { a %= M; if (a < 0) a += M; return (int)a; }
static int ord(int y) { return M / gcd(y, M); }
static int cmpd(const void *x, const void *y) { return *(int *)y - *(int *)x; }
static int cmpi(const void *x, const void *y) { return *(int *)x - *(int *)y; }
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
static int A0prof[6];
static void profile(const int *a, int *o) { for (int i = 0; i < 6; i++) o[i] = ord(a[i]); qsort(o, 6, sizeof(int), cmpd); }
static int success(const int *b, int n) {
  if (n <= 4) return 1;
  if (n != 6) return 0;
  if (!generates(b, 6) || split3(b)) return 1;
  int p[6]; profile(b, p);
  for (int i = 0; i < 6; i++) { if (p[i] < A0prof[i]) return 1; if (p[i] > A0prof[i]) return 0; }
  return 0;
}
/* apply standard multiset sig (k elements) to b (n elements) into out */
static int apply(const int *b, int n, const int *sig, int k, int *out) {
  int used[64] = {0}, c = 0;
  int miss[16], nm = 0;
  for (int j = 0; j < k; j++) { int f = -1;
    for (int i = 0; i < n; i++) if (!used[i] && b[i] == sig[j]) { f = i; break; }
    if (f >= 0) used[f] = 1; else miss[nm++] = sig[j]; }
  if (nm == k) return -1;
  for (int i = 0; i < n; i++) if (!used[i]) out[c++] = b[i];
  for (int j = 0; j < nm; j++) out[c++] = md(-miss[j]);
  c = depair(out, c);
  qsort(out, c, sizeof(int), cmpi);
  return c;
}
static int sigs_for(int y, int (*sg)[16], int *len) {
  int ns = 0;
  for (int pi = 0; pi < np; pi++) { int l = prm[pi], d = M / l;
    if (l == 2) {
      if (md(2L * y) != 0 && y != M / 2) { int x = y; sg[ns][0] = x; sg[ns][1] = md(x + M / 2); sg[ns][2] = md(-2L * x); sg[ns][3] = M / 2; len[ns++] = 4; }
      /* y = -2x */
      if (y % 2 == 0 || (M / 2) % 2 == 1) { for (int x = 1; x < M; x++) if (md(-2L * x) == y && md(2L * x) != 0) { sg[ns][0] = x; sg[ns][1] = md(x + M / 2); sg[ns][2] = y; sg[ns][3] = M / 2; len[ns++] = 4; break; } }
    } else {
      if (md((long)l * y) != 0) { for (int j = 0; j < l; j++) sg[ns][j] = md(y + (long)j * d); sg[ns][l] = md(-(long)l * y); len[ns++] = l + 1; }
      for (int x = 1; x < M; x++) if (md(-(long)l * x) == y && md((long)l * x) != 0) { for (int j = 0; j < l; j++) sg[ns][j] = md(x + (long)j * d); sg[ns][l] = y; len[ns++] = l + 1; break; }
    }
  }
  return ns;
}
static long nodes;
static int search(const int *b, int n, int depth) {
  if (success(b, n)) return 1;
  if (depth == 0) return 0;
  nodes++;
  for (int i = 0; i < n; i++) { if (i && b[i] == b[i - 1]) continue;
    int sg[48][16], len[48]; int ns = sigs_for(b[i], sg, len);
    for (int s = 0; s < ns; s++) { if (len[s] > 15) continue;
      int out[64]; int c = apply(b, n, sg[s], len[s], out);
      if (c < 0 || c > CAP) continue;
      if (search(out, c, depth - 1)) return 1; } }
  return 0;
}
static int pre6(const int *a) { if (!generates(a, 6) || split3(a)) return 0; for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++) if (md(a[i] + a[j]) == 0) return 0; return 1; }
#include "enum6.h"
static long tot = 0, nres = 0;
static void visit(const int *a) {
  tot++;
  int b[6]; memcpy(b, a, sizeof b); qsort(b, 6, sizeof(int), cmpi);
  profile(a, A0prof);
  int ok = 0;
  for (int d = 1; d <= DEPTH && !ok; d++) ok = search(b, 6, d);
  if (!ok) { nres++; printf("R %d %d %d %d %d %d\n", a[0], a[1], a[2], a[3], a[4], a[5]); fflush(stdout); }
}
int main(int argc, char **argv) {
  M = atoi(argv[1]); if (argc > 2) DEPTH = atoi(argv[2]); if (argc > 3) CAP = atoi(argv[3]);
  for (int t = 1; t < M; t++) if (gcd(t, M) == 1) { units[nu++] = t; if (2 * t < M) half[nh++] = t; }
  { int r = M; for (int p = 2; p <= r; p++) if (r % p == 0) { prm[np++] = p; while (r % p == 0) r /= p; } }
  enum6(visit);
  printf("S M=%d orbits=%ld residual=%ld depth=%d cap=%d\n", M, tot, nres, DEPTH, CAP);
  return 0;
}
