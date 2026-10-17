/* Local configurations at a maximal prime-to-6 part e' with 2,3-part
   D = 2^v 3^w.  Level N = D e'.  An e'-element is x in Z/N with gcd(x,e')=1.
   A configuration is a multiset B of 1..6 e'-elements such that the
   e'-primitive part of the balance function vanishes:
       P' sum_{x in B} v_x = 0,  v_x(t) = (t x mod N), t in (Z/N)^x,
   P' = prod_{p | e'} (|K_p| - sum_{k in K_p} R_k),  K_p = {t = 1 mod N/p}.
   Filters: no pair, no T-pair {x, x+N/2} (v >= 1), no fibre move
   (>= (l+1)/2 distinct elements of one order e, l | e, e != l, in x+(N/l)Z,
   for l = 3 (w >= 1) and l | e').  Prints canonical forms (lex-min over units)
   with flags c (x and -2x in B) and d (x and 2x+N/2 in B).
   usage: locDK e' v w maxn K   (K = power of 2: the triple table is built in K passes,
   pass k holding the sums with (hash & (K-1)) == k; same output as locD) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned long long u64;
static int KP = 1;
static int ep, v, w, D, N, nu, *U, *uidx, ne, *E, *eidx, pr[12], np, maxn = 6;
static u64 *H;
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a < 0 ? -a : a; }
static int md(long a) { a %= N; if (a < 0) a += N; return (int)a; }
static int ord(int x) { return N / gcd(x, N); }
static u64 rng = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
typedef struct { u64 h; short a, b, c; } Ent;
static int cmpe(const void *x, const void *y) { u64 a = ((const Ent *)x)->h, b = ((const Ent *)y)->h; return a < b ? -1 : a > b; }
static int cmpi(const void *a, const void *b) { return *(int *)a - *(int *)b; }
#define HC (1<<23)
static u64 *hset; static long found = 0;
static int hadd(u64 k) { u64 i = k % HC; while (hset[i]) { if (hset[i] == k) return 0; i = (i + 1) % HC; } hset[i] = k; return 1; }
static long long *Pv; /* exact projected vectors, ne x nu */
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
  printf("\n");
}
int main(int argc, char **argv) {
  ep = atoi(argv[1]); v = atoi(argv[2]); w = atoi(argv[3]); if (argc > 4) maxn = atoi(argv[4]); if (argc > 5) KP = atoi(argv[5]);
  D = 1; for (int i = 0; i < v; i++) D *= 2; for (int i = 0; i < w; i++) D *= 3; N = D * ep;
  U = malloc(N * sizeof(int)); uidx = malloc(N * sizeof(int)); E = malloc(N * sizeof(int)); eidx = malloc(N * sizeof(int));
  for (int t = 1; t < N; t++) { uidx[t] = -1; if (gcd(t, N) == 1) { uidx[t] = nu; U[nu++] = t; } }
  for (int x = 0; x < N; x++) { eidx[x] = -1; if (gcd(x, ep) == 1) { eidx[x] = ne; E[ne++] = x; } }
  { int r = ep; for (int p = 2; p <= r; p++) if (r % p == 0) { pr[np++] = p; while (r % p == 0) r /= p; } }
  /* K_p as lists of unit indices */
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
  /* representatives of orders */
  int reps[64], nr = 0;
  for (int i = 0; i < ne; i++) { int o = ord(E[i]), dup = 0; for (int r = 0; r < nr; r++) if (ord(E[reps[r]]) == o) dup = 1; if (!dup) reps[nr++] = i; }
  long tot = 1 + ne + (long)ne * (ne + 1) / 2 + (maxn >= 6 ? (long)ne * (ne + 1) * (ne + 2) / 6 : 0);
  long cap = tot / KP + tot / (8 * KP) + (1L << 20);
  Ent *tab = malloc(cap * sizeof(Ent));
  if (!tab) { fprintf(stderr, "alloc fail\n"); return 1; }
  hset = calloc(HC, sizeof(u64));
  u64 msk = (u64)KP - 1;
  for (u64 pass = 0; pass < (u64)KP; pass++) {
    long nt = 0;
#define PUT(hh, A, B, C) do { u64 h_ = (hh); if ((((h_) * 0x9E3779B97F4A7C15ULL) >> 40 & msk) == pass) { if (nt >= cap) { fprintf(stderr, "cap\n"); return 1; } tab[nt++] = (Ent){h_, A, B, C}; } } while (0)
    PUT(0, -1, -1, -1);
    for (int a = 0; a < ne; a++) { PUT(H[a], a, -1, -1);
      for (int b = a; b < ne; b++) { u64 hab = H[a] + H[b]; PUT(hab, a, b, -1);
        if (maxn >= 6) for (int c = b; c < ne; c++) PUT(hab + H[c], a, b, c); } }
    qsort(tab, nt, sizeof(Ent), cmpe);
    for (int r = 0; r < nr; r++) { int x0 = reps[r];
      for (int a = -1; a < ne; a++) for (int b = (a < 0 ? -1 : a); b < ne; b++) {
        if (a < 0 && b >= 0) continue;
        u64 L = H[x0] + (a >= 0 ? H[a] : 0) + (b >= 0 ? H[b] : 0);
        u64 tg = -L;
        if (((tg * 0x9E3779B97F4A7C15ULL) >> 40 & msk) != pass) continue;
        long lo = 0, hi = nt; while (lo < hi) { long mid = (lo + hi) / 2; if (tab[mid].h < tg) lo = mid + 1; else hi = mid; }
        for (long i = lo; i < nt && tab[i].h == tg; i++) {
          n = 0; sel[n++] = x0; if (a >= 0) sel[n++] = a; if (b >= 0) sel[n++] = b;
          if (tab[i].a >= 0) sel[n++] = tab[i].a; if (tab[i].b >= 0) sel[n++] = tab[i].b; if (tab[i].c >= 0) sel[n++] = tab[i].c;
          if (n > maxn) continue;
          if (exact()) report(); } } }
    fflush(stdout);
    fprintf(stderr, "pass %llu/%d entries %ld found %ld\n", (unsigned long long)pass, KP, nt, found); }
  fprintf(stderr, "e'=%d v=%d w=%d N=%d found=%ld\n", ep, v, w, N, found);
  return 0;
}
