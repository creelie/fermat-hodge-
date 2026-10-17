/* locF: as locE, but one table per order of x0.  Orders are ranked by class
   size (ascending); x0 is the element of B of largest rank, so all elements
   of B have rank <= rank(x0).  Memory one table of O(ne^2), time about
   1.5 ne^3/6 at D = 72.
   Local configurations at a part e' prime to 6 with 2,3-part D = 2^v 3^w.
   Same definitions and output as locD.c, with a meet-in-the-middle split
   that stores the small side (x0 + at most two elements, x0 a representative
   of an order) and enumerates the other side (at most three elements), so
   that memory is O(nr ne^2) instead of O(ne^3).
   An e'-element is x in Z/N, N = D e', with gcd(x, e') = 1.  A configuration
   is a multiset B of 1..maxn e'-elements with P' sum_{x in B} v_x = 0,
   v_x(t) = (t x mod N) for units t, P' = prod_{p | e'} (|K_p| - sum_{k in K_p} R_k),
   K_p = {t = 1 mod N/p}.  Filters: no pair, no T-pair (v >= 1), no fibre
   move for l = 3 (w >= 1) and l | e'.  Prints canonical forms (lex-min over
   units) with flags c (x, -2x in B) and d (x, 2x + N/2 in B).
   usage: locE e' v w [maxn] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned long long u64;
static int ep, v, w, D, N, nu, *U, *uidx, ne, *E, pr[12], np, maxn = 6;
static u64 *H;
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a < 0 ? -a : a; }
static int md(long a) { a %= N; if (a < 0) a += N; return (int)a; }
static int ord(int x) { return N / gcd(x, N); }
static u64 rng = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
typedef struct { u64 h; int x0, a, b; } Ent; /* a, b = -1 if absent */
static int cmpe(const void *x, const void *y) { u64 a = ((const Ent *)x)->h, b = ((const Ent *)y)->h; return a < b ? -1 : a > b; }
static int cmpi(const void *a, const void *b) { return *(int *)a - *(int *)b; }
#define HC (1<<24)
static u64 *hset; static long found = 0, hits = 0;
static int hadd(u64 k) { u64 i = k % HC; while (hset[i]) { if (hset[i] == k) return 0; i = (i + 1) % HC; } hset[i] = k; return 1; }
static long long *Pv;
static int sel[8], n;
static int exact(void) {
  for (int t = 0; t < nu; t++) { long long s = 0; for (int i = 0; i < n; i++) s += Pv[(long)sel[i] * nu + t]; if (s) return 0; }
  return 1;
}
static int filt(int *x, int k) {
  for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) if (i != j) {
    if (md(x[i] + x[j]) == 0) return 0;
    if (v >= 1 && md(x[i] + N / 2) == x[j]) return 0; }
  int ls[13], nl = 0; if (w >= 1) ls[nl++] = 3; for (int q = 0; q < np; q++) ls[nl++] = pr[q];
  for (int q = 0; q < nl; q++) { int l = ls[q], d = N / l;
    for (int i = 0; i < k; i++) { int e = ord(x[i]); if (e % l || e == l) continue;
      int cnt = 0;
      for (int j = 0; j < k; j++) { int dup = 0; for (int r = 0; r < j; r++) if (x[r] == x[j]) dup = 1; if (dup) continue;
        if (ord(x[j]) == e && md(x[j] - x[i]) % d == 0) cnt++; }
      if (2 * cnt >= l + 1) return 0; } }
  return 1;
}
/* cheap pairwise test used for pruning */
static int *NEG, *TP; /* indices of -x and x + N/2 (or -1) */
static inline int pairok(int a, int b) { return b != NEG[a] && b != TP[a]; }
static void report(void) {
  int x[8]; for (int i = 0; i < n; i++) x[i] = E[sel[i]];
  if (!filt(x, n)) return;
  int best[8], first = 1;
  for (int k = 0; k < nu; k++) { int b[8]; for (int i = 0; i < n; i++) b[i] = md((long)x[i] * U[k]);
    qsort(b, n, sizeof(int), cmpi);
    int lt = first; if (!first) for (int i = 0; i < n; i++) { if (b[i] < best[i]) { lt = 1; break; } if (b[i] > best[i]) break; }
    if (lt) { memcpy(best, b, n * sizeof(int)); first = 0; } }
  u64 h = 1469598103934665603ULL; for (int i = 0; i < n; i++) { h ^= best[i] + 7; h *= 1099511628211ULL; } h ^= n; h |= 1;
  if (!hadd(h)) return;
  found++;
  int fc = 0, fd = 0;
  for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (i != j) {
    if (md(-2L * best[i]) == best[j] && md(2L * best[i]) != 0) fc = 1;
    if (v >= 1 && md(2L * best[i] + N / 2) == best[j]) fd = 1; }
  printf("C n=%d c=%d d=%d :", n, fc, fd);
  for (int i = 0; i < n; i++) printf(" %d/%d", best[i], ord(best[i]));
  printf("\n"); fflush(stdout);
}
static u64 *TG; static int *EE; static unsigned *BK;
static Ent *tab; static long nt; static unsigned *bidx; static int BB;
static void lookup(u64 tg, int c, int d, int e) {
  unsigned bk = (unsigned)(tg >> (64 - BB));
  for (long i = bidx[bk]; i < bidx[bk + 1]; i++) { if (tab[i].h != tg) continue;
    n = 0; sel[n++] = tab[i].x0; if (tab[i].a >= 0) sel[n++] = tab[i].a; if (tab[i].b >= 0) sel[n++] = tab[i].b;
    if (c >= 0) sel[n++] = c; if (d >= 0) sel[n++] = d; if (e >= 0) sel[n++] = e;
    if (n > maxn) continue;
    hits++;
    { int bad = 0; for (int i = 0; i < n && !bad; i++) for (int j = i + 1; j < n; j++) if (!pairok(sel[i], sel[j])) { bad = 1; break; }
      if (bad) continue; }
    if (exact()) report(); }
}
int main(int argc, char **argv) {
  ep = atoi(argv[1]); v = atoi(argv[2]); w = atoi(argv[3]); if (argc > 4) maxn = atoi(argv[4]);
  D = 1; for (int i = 0; i < v; i++) D *= 2; for (int i = 0; i < w; i++) D *= 3; N = D * ep;
  U = malloc(N * sizeof(int)); uidx = malloc(N * sizeof(int)); E = malloc(N * sizeof(int));
  for (int t = 1; t < N; t++) { uidx[t] = -1; if (gcd(t, N) == 1) { uidx[t] = nu; U[nu++] = t; } }
  int *eix = malloc(N * sizeof(int));
  for (int x = 0; x < N; x++) { eix[x] = -1; if (gcd(x, ep) == 1) { eix[x] = ne; E[ne++] = x; } }
  NEG = malloc(ne * sizeof(int)); TP = malloc(ne * sizeof(int));
  for (int i = 0; i < ne; i++) { NEG[i] = eix[md(-(long)E[i])]; TP[i] = v >= 1 ? eix[md((long)E[i] + N / 2)] : -1; }
  { int r = ep; for (int p = 2; p <= r; p++) if (r % p == 0) { pr[np++] = p; while (r % p == 0) r /= p; } }
  int *K[12], Ks[12];
  for (int q = 0; q < np; q++) { K[q] = malloc(nu * sizeof(int)); Ks[q] = 0;
    for (int k = 0; k < nu; k++) if ((U[k] - 1) % (N / pr[q]) == 0) K[q][Ks[q]++] = k; }
  Pv = malloc((long)ne * nu * sizeof(long long));
  long long *tmp = malloc(nu * sizeof(long long)), *cur = malloc(nu * sizeof(long long));
  for (int i = 0; i < ne; i++) {
    for (int k = 0; k < nu; k++) cur[k] = md((long)U[k] * E[i]);
    for (int q = 0; q < np; q++) {
      for (int k = 0; k < nu; k++) { long long s = 0; for (int j = 0; j < Ks[q]; j++) s += cur[uidx[md((long)U[k] * U[K[q][j]])]]; tmp[k] = (long long)Ks[q] * cur[k] - s; }
      memcpy(cur, tmp, nu * sizeof(long long)); }
    memcpy(Pv + (long)i * nu, cur, nu * sizeof(long long)); }
  u64 *R = malloc(nu * sizeof(u64)); for (int k = 0; k < nu; k++) R[k] = rnd();
  H = malloc(ne * sizeof(u64));
  for (int i = 0; i < ne; i++) { u64 s = 0; for (int k = 0; k < nu; k++) s += R[k] * (u64)Pv[(long)i * nu + k]; H[i] = s; }
  int reps[64], nr = 0, csz[64];
  for (int i = 0; i < ne; i++) { int o = ord(E[i]), dup = -1; for (int r = 0; r < nr; r++) if (ord(E[reps[r]]) == o) dup = r; if (dup < 0) { csz[nr] = 1; reps[nr++] = i; } else csz[dup]++; }
  /* sort classes ascending by size (ties by order) */
  for (int i = 0; i < nr; i++) for (int j = i + 1; j < nr; j++) {
    int oi = ord(E[reps[i]]), oj = ord(E[reps[j]]);
    if (csz[j] < csz[i] || (csz[j] == csz[i] && oj < oi)) { int t = reps[i]; reps[i] = reps[j]; reps[j] = t; t = csz[i]; csz[i] = csz[j]; csz[j] = t; } }
  int *rk = malloc(ne * sizeof(int));
  for (int i = 0; i < ne; i++) for (int r = 0; r < nr; r++) if (ord(E[i]) == ord(E[reps[r]])) rk[i] = r;
  int *L = malloc(ne * sizeof(int)); TG = malloc(ne * sizeof(u64)); EE = malloc(ne * sizeof(int)); BK = malloc(ne * sizeof(unsigned));
  hset = calloc(HC, sizeof(u64));
  long ntmax = 0;
  for (int r = 0; r < nr; r++) { int x0 = reps[r], nl = 0;
    for (int i = 0; i < ne; i++) if (rk[i] <= r) L[nl++] = i;
    long cap = 1 + nl + (long)nl * (nl + 1) / 2;
    tab = malloc(cap * sizeof(Ent)); nt = 0;
    tab[nt++] = (Ent){H[x0], x0, -1, -1};
    for (int ia = 0; ia < nl; ia++) { int a = L[ia]; if (!pairok(x0, a)) continue;
      tab[nt++] = (Ent){H[x0] + H[a], x0, a, -1};
      if (maxn >= 3) for (int ib = ia; ib < nl; ib++) { int b = L[ib]; if (!pairok(x0, b) || !pairok(a, b)) continue;
        tab[nt++] = (Ent){H[x0] + H[a] + H[b], x0, a, b}; } }
    if (nt > ntmax) ntmax = nt;
    qsort(tab, nt, sizeof(Ent), cmpe);
    BB = 1; while ((1L << BB) < nt && BB < 28) BB++;
    bidx = malloc(((1L << BB) + 1) * sizeof(unsigned));
    { long i = 0; for (long bk = 0; bk <= (1L << BB); bk++) { while (i < nt && (bk == (1L << BB) || (tab[i].h >> (64 - BB)) < (u64)bk)) i++; bidx[bk] = (unsigned)i; } }
    lookup((u64)0, -1, -1, -1);
    for (int ic = 0; ic < nl; ic++) { int c = L[ic];
      lookup(-H[c], c, -1, -1);
      if (maxn >= 5) for (int id = ic; id < nl; id++) { int d = L[id]; if (!pairok(c, d)) continue;
        lookup(-(H[c] + H[d]), c, d, -1);
        if (maxn >= 6) { int m = 0; u64 base = H[c] + H[d];
          for (int ie = id; ie < nl; ie++) { int e = L[ie]; if (!pairok(c, e) || !pairok(d, e)) continue;
            u64 tg = -(base + H[e]); TG[m] = tg; EE[m] = e; BK[m] = (unsigned)(tg >> (64 - BB)); m++; }
          /* software-pipelined lookups: prefetch bucket index, then table row */
          for (int i = 0; i < m; i++) {
            if (i + 16 < m) __builtin_prefetch(&bidx[BK[i + 16]]);
            if (i + 8 < m) { unsigned lo = bidx[BK[i + 8]]; if (lo < bidx[BK[i + 8] + 1]) __builtin_prefetch(&tab[lo]); }
            unsigned lo = bidx[BK[i]], hi = bidx[BK[i] + 1];
            if (lo == hi) continue;
            for (unsigned j = lo; j < hi; j++) if (tab[j].h == TG[i]) { lookup(TG[i], c, d, EE[i]); break; } } } } }
    free(tab); free(bidx);
    fprintf(stderr, "  rank %d order %d class %d nl %d done\n", r, ord(E[x0]), csz[r], nl); }
  fprintf(stderr, "e'=%d v=%d w=%d N=%d ne=%d ntmax=%ld hits=%ld found=%ld\n", ep, v, w, N, ne, ntmax, hits, found);
  return 0;
}
