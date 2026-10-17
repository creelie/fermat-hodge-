/* Local configurations at a maximal odd part e* whose largest order is 4e*
   (M even, prime to 3).  Elements with odd part e*, parametrised by v in
   U* = (Z/e*)^x:
     type 0  x_{+,v} = (M/4e*)u, u = 1 mod 4, u = v mod e*   (order 4e*)
     type 1  x_{-,v} = (M/4e*)u, u = 3 mod 4, u = v mod e*   (order 4e*)
     type 2  y_v     = (M/2e*)u, u odd,       u = v mod e*   (order 2e*)
     type 3  z_v     = (M/e*)v                               (order e*)
   Relations (lem:charrel at conductors e* and 4e*):
     (R1) the odd part of H = 2Z + 2Y - 2Y(2.) + X - X(2.) is split,
     (R2) the even part of Q = mult(x_+) - mult(x_-) is split,
   where split means killed by P_new = prod_p (1 - average over K_p).
   Excluded: pairs, T-pairs, a with -2a when this lowers (x with y_{-v},
   y_v with z_{-v}), and fibre lines (>= (p+1)/2 distinct elements of one
   type in a coset of K_p; for type 3 only when e* != p).
   The first element is normalised to x_{+,1}.  Sizes 1..6.
   usage: loc4 e*   */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned long long u64;
static int es, nu, U[4096], idx[8192], pr[12], np;
static long long *Pi;
static u64 *R1, *R2, *HV1, *HV2, *HT;
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
static int sel[8], N, half2;
static int neg(int v) { return es - v; }
static int hlf(int v) { return (int)((long)v * half2 % es); }
/* signed delta contributions: rel 1 and rel 2 */
static int contrib(int t, int v, int *vs, int *sg, int rel) {
  int k = 0;
  if (rel == 1) {
    int c = (t == 3 || t == 2) ? 2 : 1;
    vs[k] = v; sg[k++] = c; vs[k] = neg(v); sg[k++] = -c;
    if (t != 3) { int h = hlf(v); vs[k] = h; sg[k++] = -c; vs[k] = neg(h); sg[k++] = c; }
  } else {
    if (t == 0) { vs[k] = v; sg[k++] = 1; vs[k] = neg(v); sg[k++] = 1; }
    if (t == 1) { vs[k] = v; sg[k++] = -1; vs[k] = neg(v); sg[k++] = -1; }
  }
  return k;
}
static int check(void) {
  for (int i = 0; i < N; i++) for (int j = i + 1; j < N; j++) {
    int ti = sel[i] / nu, tj = sel[j] / nu, vi = U[sel[i] % nu], vj = U[sel[j] % nu];
    /* pairs */
    if (ti == tj && ti >= 2 && (vi + vj) % es == 0) return 0;
    if (ti + tj == 1 && (vi + vj) % es == 0) return 0;
    /* T-pairs */
    if (ti + tj == 1 && vi == vj) return 0;
    if (ti == 2 && tj == 3 && hlf(vi) == vj) return 0;
    if (ti == 3 && tj == 2 && hlf(vj) == vi) return 0;
    /* a with -2a */
    if (ti <= 1 && tj == 2 && (vi + vj) % es == 0) return 0;
    if (tj <= 1 && ti == 2 && (vi + vj) % es == 0) return 0;
    if (ti == 2 && tj == 3 && (vi + vj) % es == 0) return 0;
    if (ti == 3 && tj == 2 && (vi + vj) % es == 0) return 0;
  }
  for (int p = 0; p < np; p++) { int P = pr[p];
    for (int t = 0; t < 4; t++) { if (t == 3 && P == es) continue;
      for (int i = 0; i < N; i++) { if (sel[i] / nu != t) continue; int v = U[sel[i] % nu], cnt = 0;
        for (int j = 0; j < N; j++) { if (sel[j] / nu != t) continue; int w = U[sel[j] % nu];
          if ((w - v) % (es / P) == 0) { int dup = 0; for (int k = 0; k < j; k++) if (sel[k] == sel[j]) dup = 1; if (!dup) cnt++; } }
        if (2 * cnt >= P + 1) return 0; } } }
  static long long acc[4096];
  for (int rel = 1; rel <= 2; rel++) {
    memset(acc, 0, sizeof(long long) * nu);
    for (int i = 0; i < N; i++) { int t = sel[i] / nu, v = U[sel[i] % nu];
      int vs[4], sg[4], k = contrib(t, v, vs, sg, rel);
      for (int q = 0; q < k; q++) { int iv = inv(vs[q]);
        for (int w = 0; w < nu; w++) acc[w] += sg[q] * Pi[idx[(long)U[w] * iv % es]]; } }
    for (int w = 0; w < nu; w++) if (acc[w]) return 0; }
  return 1;
}
static const char *TN = "ABYZ";
static void report(void) {
  /* canonical form under v -> v*t for units t, and the sign flip
     (t = -1 mod 4) which swaps types 0 and 1 */
  int best[8], first = 1;
  for (int fl = 0; fl < 2; fl++)
  for (int k = 0; k < nu; k++) { int b[8];
    for (int i = 0; i < N; i++) { int t = sel[i] / nu, v = U[sel[i] % nu];
      if (fl && t <= 1) t = 1 - t;
      b[i] = t * es + (int)((long)v * U[k] % es); }
    qsort(b, N, sizeof(int), cmpi);
    int lt = first; if (!first) for (int i = 0; i < N; i++) { if (b[i] < best[i]) { lt = 1; break; } if (b[i] > best[i]) break; }
    if (lt) { memcpy(best, b, N * sizeof(int)); first = 0; } }
  u64 h = 1469598103934665603ULL; for (int i = 0; i < N; i++) { h ^= best[i] + 7; h *= 1099511628211ULL; } h ^= N; h |= 1;
  if (!hadd(h)) return;
  found++;
  int cnt[4] = {0};
  for (int i = 0; i < N; i++) cnt[best[i] / es]++;
  printf("C n=%d A=%d B=%d Y=%d Z=%d :", N, cnt[0], cnt[1], cnt[2], cnt[3]);
  for (int i = 0; i < N; i++) printf(" %c%d", TN[best[i] / es], best[i] % es);
  printf("\n");
}
static u64 hashrel(int t, int v) {
  int vs[4], sg[4]; u64 s = 0;
  int k = contrib(t, v, vs, sg, 1);
  for (int q = 0; q < k; q++) s += (u64)(long long)sg[q] * HV1[idx[vs[q]]];
  k = contrib(t, v, vs, sg, 2);
  for (int q = 0; q < k; q++) s += (u64)(long long)sg[q] * HV2[idx[vs[q]]];
  return s;
}
int main(int argc, char **argv) {
  es = atoi(argv[1]);
  for (int v = 1; v < es; v++) if (gcd(v, es) == 1) { idx[v] = nu; U[nu++] = v; }
  half2 = (es + 1) / 2;
  { int r = es; for (int p = 2; p <= r; p++) if (r % p == 0) { pr[np++] = p; while (r % p == 0) r /= p; } }
  long long Kall = 1; int Ksz[12];
  for (int p = 0; p < np; p++) { int c = 0; for (int k = 0; k < nu; k++) if ((U[k] - 1) % (es / pr[p]) == 0) c++; Ksz[p] = c; Kall *= c; }
  Pi = calloc(nu, sizeof(long long));
  for (int S = 0; S < (1 << np); S++) { long mod = es; long long ks = 1;
    for (int p = 0; p < np; p++) if (S >> p & 1) { mod /= pr[p]; ks *= Ksz[p]; }
    int sg = __builtin_popcount(S) & 1 ? -1 : 1;
    for (int k = 0; k < nu; k++) if ((U[k] - 1) % mod == 0) Pi[k] += sg * (Kall / ks); }
  R1 = malloc(nu * sizeof(u64)); R2 = malloc(nu * sizeof(u64));
  HV1 = malloc(nu * sizeof(u64)); HV2 = malloc(nu * sizeof(u64));
  for (int k = 0; k < nu; k++) { R1[k] = rnd(); R2[k] = rnd(); }
  for (int k = 0; k < nu; k++) { u64 s1 = 0, s2 = 0;
    for (int j = 0; j < nu; j++) { s1 += R1[idx[(long)U[j] * U[k] % es]] * (u64)Pi[j]; s2 += R2[idx[(long)U[j] * U[k] % es]] * (u64)Pi[j]; }
    HV1[k] = s1; HV2[k] = s2; }
  int T = 4 * nu;
  HT = malloc(T * sizeof(u64));
  for (int e = 0; e < T; e++) HT[e] = hashrel(e / nu, U[e % nu]);
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
