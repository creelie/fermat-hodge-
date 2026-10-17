/* Local configurations at a maximal order e = 2e*, e* odd, prime to 3.
   Elements of order e are (0,v), of order e* are (1,v), v in U* = units mod e*.
   Enumerate multisets of N <= 6 such elements containing (0,1), with
   no pair, no T-pair ((0,v),(1,v) both present), no fiber line
   (>= (p+1)/2 distinct elements of one type in a coset of K_p, p | e*,
   and p != e* for type 1), and Psi(w) = F(w) - F(2w) + E(2w) split.
   Prints canonical representatives (min over units). usage: loc2 e* */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int es, U[2000], nu, idx[4000], pr[10], np, sub[10][2000], ns[10];
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int sel[8], N;
static long found = 0;
static int cmpi(const void *a, const void *b) { return *(int *)a - *(int *)b; }
#define HC (1<<20)
static unsigned long long hset[HC];
static int hadd(unsigned long long k) { unsigned long long i = k % HC; while (hset[i]) { if (hset[i] == k) return 0; i = (i + 1) % HC; } hset[i] = k; return 1; }
static int check(int n) {
  int F[2000] = {0}, E[2000] = {0};
  for (int i = 0; i < n; i++) { int t = sel[i] / nu, v = U[sel[i] % nu];
    int *f = t ? E : F; f[v]++; f[es - v]--; }
  /* no pair: |F(v)| equals multiplicity, i.e. no v with both +v and -v */
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
    int ti = sel[i] / nu, tj = sel[j] / nu, vi = U[sel[i] % nu], vj = U[sel[j] % nu];
    if (ti == tj && (vi + vj) % es == 0) return 0;
    if (ti != tj && vi == vj) return 0; }
  /* fiber lines */
  for (int p = 0; p < np; p++) { int P = pr[p];
    for (int t = 0; t < 2; t++) { if (t == 1 && P == es) continue;
      for (int i = 0; i < n; i++) { if (sel[i] / nu != t) continue; int v = U[sel[i] % nu], cnt = 0;
        int seen[8] = {0};
        for (int j = 0; j < n; j++) { if (sel[j] / nu != t) continue; int w = U[sel[j] % nu];
          /* same coset of K_p: w/v in K_p  <=>  w == v mod es/P */
          if ((w - v) % (es / P) == 0) { int dup = 0; for (int k = 0; k < j; k++) if (sel[k] == sel[j] && sel[k] / nu == t) dup = 1; if (!dup) cnt++; } }
        (void)seen; if (2 * cnt >= P + 1) return 0; } } }
  /* Psi and splitness */
  double Psi[2000];
  for (int k = 0; k < nu; k++) { int w = U[k]; Psi[w] = F[w] - F[2 * w % es] + E[2 * w % es]; }
  for (int k = 0; k < nu; k++) { int w = U[k]; double s = 0;
    for (int S = 0; S < (1 << np); S++) { /* average over prod_{p in S} K_p of Psi(w*k) */
      int sg = __builtin_popcount(S) & 1 ? -1 : 1;
      /* elements u with u == 1 mod es/prod(S)... product of K_p over p in S = units == 1 mod es/prod */
      long q = 1; for (int p = 0; p < np; p++) if (S >> p & 1) q *= pr[p];
      /* careful: product of K_p (p in S) = units congruent to 1 mod es/rad_S where we need es/q... */
      long mod = es; for (int p = 0; p < np; p++) if (S >> p & 1) mod /= pr[p];
      double a = 0; int c = 0;
      for (int j = 0; j < nu; j++) if ((U[j] - 1) % mod == 0) { a += Psi[(long)w * U[j] % es]; c++; }
      s += sg * a / c; }
    if (s > 1e-9 || s < -1e-9) return 0; }
  return 1;
}
static void report(int n) {
  int best[8], first = 1;
  for (int k = 0; k < nu; k++) { int b[8]; for (int i = 0; i < n; i++) { int t = sel[i] / nu, v = U[sel[i] % nu]; b[i] = t * es + (int)((long)v * U[k] % es); }
    qsort(b, n, sizeof(int), cmpi);
    if (first || memcmp(b, best, n * sizeof(int)) < 0) { int lt = first; if (!first) for (int i = 0; i < n; i++) { if (b[i] < best[i]) { lt = 1; break; } if (b[i] > best[i]) break; } if (lt) { memcpy(best, b, n * sizeof(int)); first = 0; } } }
  unsigned long long h = 1469598103934665603ULL; for (int i = 0; i < n; i++) { h ^= best[i] + 7; h *= 1099511628211ULL; } h ^= n; h |= 1;
  if (!hadd(h)) return;
  found++;
  int ne = 0; for (int i = 0; i < n; i++) if (best[i] < es) ne++;
  printf("C n=%d ne=%d :", n, ne);
  for (int i = 0; i < n; i++) printf(" %s%d", best[i] < es ? "F" : "E", best[i] % es);
  /* sum of the elements as (n_e mod 2, sum of v) */
  long sv = 0; for (int i = 0; i < n; i++) sv += best[i] % es;
  printf("  | sum=(%d,%ld)\n", ne % 2, sv % es);
}
static void rec(int pos, int start, int nmax) {
  if (pos >= 1 && check(pos)) report(pos);
  if (pos == nmax) return;
  for (int i = start; i < 2 * nu; i++) { sel[pos] = i; rec(pos + 1, i, nmax); }
}
int main(int argc, char **argv) {
  es = atoi(argv[1]); int nmax = argc > 2 ? atoi(argv[2]) : 6;
  for (int v = 1; v < es; v++) if (gcd(v, es) == 1) { idx[v] = nu; U[nu++] = v; }
  { int r = es; for (int p = 2; p <= r; p++) if (r % p == 0) { pr[np++] = p; while (r % p == 0) r /= p; } }
  /* first element (F,1) = index 0; then nondecreasing */
  sel[0] = 0; if (check(1)) report(1);
  for (int n = 2; n <= nmax; n++) ;
  /* recursion over remaining positions with start 0 */
  { void rec2(int pos, int start); }
  /* simple: positions 1..nmax-1 with indices >= 0 nondecreasing */
  rec(1, 0, nmax);
  fprintf(stderr, "e*=%d found=%ld\n", es, found);
  return 0;
}
