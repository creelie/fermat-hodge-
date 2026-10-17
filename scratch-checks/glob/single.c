/* Completions of a local configuration B at a unique maximal prime-to-6 part e
   by one or two low elements, at a level M (multiple of the level of B).
   Low elements have prime-to-6 part a proper divisor of e.  Prints the
   balanced sextuples B + low that contain no pair, generate Z/M and are not
   the union of two zero-sum triples.
   usage: single M e Dlevel x1 x2 ... (elements of B at level Dlevel*e) */
#include <stdio.h>
#include <stdlib.h>
static long M, e, *U, nu;
static long gcd(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a < 0 ? -a : a; }
static long p6(long n) { while (n % 2 == 0) n /= 2; while (n % 3 == 0) n /= 3; return n; }
static long ord(long x) { return M / gcd(x, M); }
static int okpart(long x) { long f = p6(ord(x)); return f != e && e % f == 0; }
int main(int argc, char **argv) {
  M = atol(argv[1]); e = atol(argv[2]); long Dl = atol(argv[3]); int nb = argc - 4;
  long A[8], s = M / (Dl * e);
  for (int i = 0; i < nb; i++) A[i] = (atol(argv[4 + i]) * s) % M;
  U = malloc(M * sizeof(long)); nu = 0;
  for (long t = 1; t < M; t++) if (gcd(t, M) == 1) U[nu++] = t;
  long *d = malloc(nu * sizeof(long));
  for (long k = 0; k < nu; k++) { long sm = 0; for (int i = 0; i < nb; i++) sm += (U[k] * A[i]) % M; d[k] = 3 * M - sm; }
  int nl = 6 - nb; long cnt = 0;
  if (nl == 1) {
    long a = d[0];
    if (a > 0 && a < M) { int ok = 1; for (long k = 0; k < nu && ok; k++) if ((U[k] * a) % M != d[k]) ok = 0;
      if (ok) { A[nb] = a; nb++; goto check1; } }
    return 0;
  check1:;
    long g = M; for (int i = 0; i < 6; i++) g = gcd(g, A[i]);
    int pr = 0; for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++) if ((A[i] + A[j]) % M == 0) pr = 1;
    int sp = 0; for (int i = 1; i < 6; i++) for (int j = i + 1; j < 6; j++) if ((A[0] + A[i] + A[j]) % M == 0) sp = 1;
    if (g == 1 && !pr && !sp && okpart(A[5])) { printf("S M=%ld :", M); for (int i = 0; i < 6; i++) printf(" %ld", A[i]); printf("\n"); }
    return 0;
  }
  if (nl == 2) {
    for (long a1 = 1; a1 < M; a1++) { long a2 = d[0] - a1; if (a2 < a1 || a2 >= M) continue;
      int ok = 1; for (long k = 1; k < nu && ok; k++) if ((U[k] * a1) % M + (U[k] * a2) % M != d[k]) ok = 0;
      if (!ok) continue;
      A[nb] = a1; A[nb + 1] = a2;
      long g = M; for (int i = 0; i < 6; i++) g = gcd(g, A[i]);
      int pr = 0; for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++) if ((A[i] + A[j]) % M == 0) pr = 1;
      int sp = 0; for (int i = 1; i < 6; i++) for (int j = i + 1; j < 6; j++) if ((A[0] + A[i] + A[j]) % M == 0) sp = 1;
      if (g == 1 && !pr && !sp && okpart(a1) && okpart(a2)) { cnt++; printf("S M=%ld :", M); for (int i = 0; i < 6; i++) printf(" %ld", A[i]); printf("\n"); } }
  }
  return 0;
}
