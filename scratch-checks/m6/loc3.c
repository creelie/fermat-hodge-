/* Local configurations at a largest order e = 2e*, e* odd, prime to 3.
   Same conditions as loc2.c, found by meet in the middle on a linear hash.
   Elements of order e at v (type F) and of order e* at v (type E), v in
   U* = (Z/e*)^x.  E_1 = E - F + F(./2) must be split along (K_p), i.e.
   P_new E_1 = 0, where P_new = prod_p (1 - avg over K_p).
   usage: loc3 e*   (prints canonical configurations, first element F1) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned long long u64;
static int es, nu, U[4096], idx[8192], pr[12], np;
static long long *Pi;           /* integer multiple of P_new(delta_1) */
static u64 *R, *HV, *HT;        /* random weights, hash of pi_v, hash of types */
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int inv(int a) { for (int x = 1; x < es; x++) if ((long)a * x % es == 1) return x; return 0; }
static u64 rng = 88172645463325252ULL;
static u64 rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
typedef struct { u64 h; int a, b, c; } Ent;
static int cmpe(const void *x, const void *y) { u64 a = ((const Ent *)x)->h, b = ((const Ent *)y)->h; return a < b ? -1 : a > b; }
static int cmpi(const void *a, const void *b) { return *(int *)a - *(int *)b; }
#define HC (1<<22)
static u64 *hset;
static int hadd(u64 k) { u64 i = k % HC; while (hset[i]) { if (hset[i] == k) return 0; i = (i + 1) % HC; } hset[i] = k; return 1; }
static long found = 0;
static int sel[8], N;
static int check(void) {
  /* no pair, no T-pair */
  for (int i = 0; i < N; i++) for (int j = i + 1; j < N; j++) {
    int ti = sel[i] / nu, tj = sel[j] / nu, vi = U[sel[i] % nu], vj = U[sel[j] % nu];
    if (ti == tj && (vi + vj) % es == 0) return 0;
    if (ti != tj && vi == vj) return 0; }
  /* fiber lines: >= (p+1)/2 distinct elements of one type in a coset of K_p */
  for (int p = 0; p < np; p++) { int P = pr[p];
    for (int t = 0; t < 2; t++) { if (t == 1 && P == es) continue;
      for (int i = 0; i < N; i++) { if (sel[i] / nu != t) continue; int v = U[sel[i] % nu], cnt = 0;
        for (int j = 0; j < N; j++) { if (sel[j] / nu != t) continue; int w = U[sel[j] % nu];
          if ((w - v) % (es / P) == 0) { int dup = 0; for (int k = 0; k < j; k++) if (sel[k] == sel[j]) dup = 1; if (!dup) cnt++; } }
        if (2 * cnt >= P + 1) return 0; } } }
  /* exact splitness: sum of signed pi_v vanishes */
  static long long acc[4096];
  memset(acc, 0, sizeof(long long) * nu);
  for (int i = 0; i < N; i++) { int t = sel[i] / nu, v = U[sel[i] % nu];
    int vs[4], sg[4], k = 0;
    if (t == 0) { vs[k] = v; sg[k++] = -1; vs[k] = es - v; sg[k++] = 1; vs[k] = 2 * v % es; sg[k++] = 1; vs[k] = es - 2 * v % es; sg[k++] = -1; }
    else { vs[k] = v; sg[k++] = 1; vs[k] = es - v; sg[k++] = -1; }
    for (int q = 0; q < k; q++) { int iv = inv(vs[q]);
      for (int w = 0; w < nu; w++) acc[w] += sg[q] * Pi[idx[(long)U[w] * iv % es]]; } }
  for (int w = 0; w < nu; w++) if (acc[w]) return 0;
  return 1;
}
static void report(void) {
  int best[8], first = 1;
  for (int k = 0; k < nu; k++) { int b[8]; for (int i = 0; i < N; i++) { int t = sel[i] / nu, v = U[sel[i] % nu]; b[i] = t * es + (int)((long)v * U[k] % es); }
    qsort(b, N, sizeof(int), cmpi);
    int lt = first; if (!first) for (int i = 0; i < N; i++) { if (b[i] < best[i]) { lt = 1; break; } if (b[i] > best[i]) break; }
    if (lt) { memcpy(best, b, N * sizeof(int)); first = 0; } }
  u64 h = 1469598103934665603ULL; for (int i = 0; i < N; i++) { h ^= best[i] + 7; h *= 1099511628211ULL; } h ^= N; h |= 1;
  if (!hadd(h)) return;
  found++;
  int ne = 0; for (int i = 0; i < N; i++) if (best[i] < es) ne++;
  printf("C n=%d ne=%d :", N, ne);
  for (int i = 0; i < N; i++) printf(" %s%d", best[i] < es ? "F" : "E", best[i] % es);
  printf("\n");
}
int main(int argc, char **argv) {
  es = atoi(argv[1]);
  for (int v = 1; v < es; v++) if (gcd(v, es) == 1) { idx[v] = nu; U[nu++] = v; }
  { int r = es; for (int p = 2; p <= r; p++) if (r % p == 0) { pr[np++] = p; while (r % p == 0) r /= p; } }
  long long Kall = 1; int Ksz[12];
  for (int p = 0; p < np; p++) { int c = 0; for (int k = 0; k < nu; k++) if ((U[k] - 1) % (es / pr[p]) == 0) c++; Ksz[p] = c; Kall *= c; }
  Pi = calloc(nu, sizeof(long long));
  for (int S = 0; S < (1 << np); S++) { long mod = es; long long ks = 1;
    for (int p = 0; p < np; p++) if (S >> p & 1) { mod /= pr[p]; ks *= Ksz[p]; }
    int sg = __builtin_popcount(S) & 1 ? -1 : 1;
    for (int k = 0; k < nu; k++) if ((U[k] - 1) % mod == 0) Pi[k] += sg * (Kall / ks); }
  R = malloc(nu * sizeof(u64)); HV = malloc(nu * sizeof(u64)); HT = malloc(2 * nu * sizeof(u64));
  for (int k = 0; k < nu; k++) R[k] = rnd();
  for (int k = 0; k < nu; k++) { u64 s = 0; for (int j = 0; j < nu; j++) s += R[idx[(long)U[j] * U[k] % es]] * (u64)Pi[j]; HV[k] = s; }
  for (int k = 0; k < nu; k++) { int v = U[k];
    HT[k] = -HV[k] + HV[idx[es - v]] + HV[idx[2 * v % es]] - HV[idx[es - 2 * v % es]];
    HT[nu + k] = HV[k] - HV[idx[es - v]]; }
  int T = 2 * nu;
  long cap = 1 + T + (long)T * (T + 1) / 2 + (long)T * (T + 1) * (T + 2) / 6;
  Ent *tab = malloc(cap * sizeof(Ent)); long nt = 0;
  tab[nt++] = (Ent){0, -1, -1, -1};
  for (int a = 0; a < T; a++) { tab[nt++] = (Ent){HT[a], a, -1, -1};
    for (int b = a; b < T; b++) { tab[nt++] = (Ent){HT[a] + HT[b], a, b, -1};
      for (int c = b; c < T; c++) tab[nt++] = (Ent){HT[a] + HT[b] + HT[c], a, b, c}; } }
  qsort(tab, nt, sizeof(Ent), cmpe);
  hset = calloc(HC, sizeof(u64));
  for (int a = -1; a < T; a++) for (int b = (a < 0 ? -1 : a); b < T; b++) {
    if (a < 0 && b >= 0) continue;
    u64 L = HT[0] + (a >= 0 ? HT[a] : 0) + (b >= 0 ? HT[b] : 0);
    u64 tg = -L;
    long lo = 0, hi = nt; while (lo < hi) { long mid = (lo + hi) / 2; if (tab[mid].h < tg) lo = mid + 1; else hi = mid; }
    for (long i = lo; i < nt && tab[i].h == tg; i++) {
      N = 0; sel[N++] = 0; if (a >= 0) sel[N++] = a; if (b >= 0) sel[N++] = b;
      if (tab[i].a >= 0) sel[N++] = tab[i].a; if (tab[i].b >= 0) sel[N++] = tab[i].b; if (tab[i].c >= 0) sel[N++] = tab[i].c;
      if (check()) report(); } }
  fprintf(stderr, "e*=%d found=%ld\n", es, found);
  return 0;
}
