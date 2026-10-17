/* prop.c  Propagation search for the local configurations at a prime e' = p
   with 2,3-part D = 2^V 3^W (level N = D p), or in the formal regime (p = 0),
   where the units -1, 2, 3 of Z/p are replaced by the free group {+-1} x Z^2.
   An element is x = (s mod D, u), u a unit mod p (formally u = +-2^a 3^b; a
   connected configuration lies in one coset u_0 <-1,2,3>, and u_0 = 1).
   g = gcd(s, D), d = D/g, r_x = s/g.  Relations (p >= 29, all constants zero):
   for every layer c | D with c != 2 mod 4 and every class {v, -v},
       P_c omega_c(., v) = 0,   omega_c(r, v) = nu_c(r, -v) - nu_c(-r, v),
       nu_c = sum_{x : c | d_x} (phi(D)/phi(d_x)) sum_{T subset L_x(c)} (-1)^|T|
              delta(r_x / prod T mod c, u_x / (g_x prod T)),
   L_x(c) = {l in {2,3} : l | d_x, l not | c}, P_c = prod_{l | c} (|K_l| - sum_{k in K_l} R_k),
   K_l = {k in (Z/c)^x : k = 1 mod c/l}.  Filters as in locD: no pair, no
   T-pair (s + D/2, u), no two distinct elements of one order d p with 3 | d,
   the same u and s congruent mod D/3.  A connected solution contains a cover of
   every point where the residual is not zero; branch over the covers of the
   point with fewest covers, excluding the earlier siblings (each solution with
   no proper sub-solution through the base is found).  The base is (D/d0, 1)
   for each divisor d0, and only elements with d <= d0 are added.
   Output: canonical forms (lex-min over choices of base and units),
   "F n= : s,sg,a,b ..." (formal) or "C n= c=0 d=0 : x/ord ..." (mod p).
   usage: prop V W p [maxn] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef long long ll; typedef unsigned long long u64; typedef __int128 i128;
static int V, W, D, MAXN = 6, phiD; static ll P;
static int gcdi(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a < 0 ? -a : a; }
static int phi(int n) { int r = 0; for (int i = 1; i <= n; i++) if (gcdi(i, n) == 1) r++; return r; }
static ll mulm(ll a, ll b) { return (ll)((i128)a * b % P); }
static ll powm(ll a, ll e) { ll r = 1; a %= P; if (a < 0) a += P; while (e) { if (e & 1) r = mulm(r, a); a = mulm(a, a); e >>= 1; } return r; }
static ll invm(ll a) { return powm(a, P - 2); }
#define ML 16
static int nl, lc[ML], lph[ML], lu[ML][24], lix[ML][80];
static int Pcol[ML][24][24];
typedef struct { int L, ri, al, be, m; } Ent;
static int gS[80], dS[80], nent[80]; static Ent ent[80][16];
static ll pw23[8][8], inv23[8][8];
typedef struct { int s, sg, a, b; ll u; } El;
static El S[8]; static int nS;
typedef struct { u64 key; int L; int vec[24]; } Pt;
static Pt pts[160]; static int npts;
static u64 ekey(const El *e) {
  if (P) return (u64)e->s * (u64)P + (u64)e->u;
  return ((u64)e->s << 48) | ((u64)(e->sg > 0) << 47) | ((u64)(e->a + (1 << 20)) << 24) | (u64)(e->b + (1 << 20)); }
static void ptof(const El *e, const Ent *t, u64 *key, int *pos, int *val) {
  int c = lc[t->L], sig;
  if (P) { ll v = mulm(e->u, inv23[t->al][t->be]); if (v <= (P - 1) / 2) sig = 1; else { sig = -1; v = P - v; }
    *key = ((u64)t->L << 56) | (u64)v; }
  else { sig = e->sg; *key = ((u64)t->L << 56) | ((u64)(e->a - t->al + (1 << 20)) << 24) | (u64)(e->b - t->be + (1 << 20)); }
  int r = lu[t->L][t->ri], rp = sig > 0 ? (c - r) % c : r;
  *pos = lix[t->L][rp]; *val = sig > 0 ? -t->m : t->m; }
static int findpt(u64 key) { for (int i = 0; i < npts; i++) if (pts[i].key == key) return i; return -1; }
static int addel(const El *e) {
  int old = npts;
  for (int k = 0; k < nent[e->s]; k++) { u64 key; int pos, val; const Ent *t = &ent[e->s][k]; ptof(e, t, &key, &pos, &val);
    int i = findpt(key); if (i < 0) { i = npts++; pts[i].key = key; pts[i].L = t->L; memset(pts[i].vec, 0, sizeof pts[i].vec); }
    for (int j = 0; j < lph[t->L]; j++) pts[i].vec[j] += val * Pcol[t->L][pos][j]; }
  S[nS++] = *e; return old; }
static void delel(int old) {
  El *e = &S[--nS];
  for (int k = 0; k < nent[e->s]; k++) { u64 key; int pos, val; const Ent *t = &ent[e->s][k]; ptof(e, t, &key, &pos, &val);
    int i = findpt(key); for (int j = 0; j < lph[t->L]; j++) pts[i].vec[j] -= val * Pcol[t->L][pos][j]; }
  npts = old; }
static int nonzero(const Pt *q) { for (int j = 0; j < lph[q->L]; j++) if (q->vec[j]) return 1; return 0; }
static int ueq(const El *x, const El *y) { return P ? x->u == y->u : (x->sg == y->sg && x->a == y->a && x->b == y->b); }
static int uneg(const El *x, const El *y) { return P ? x->u == P - y->u : (x->sg == -y->sg && x->a == y->a && x->b == y->b); }
static int okadd(const El *y) {
  for (int i = 0; i < nS; i++) { const El *x = &S[i];
    if (x->s == (D - y->s) % D && uneg(x, y)) return 0;
    if (V >= 1 && ueq(x, y) && x->s == (y->s + D / 2) % D) return 0;
    if (W >= 1 && dS[y->s] % 3 == 0 && ueq(x, y) && x->s != y->s && dS[x->s] == dS[y->s] && (x->s - y->s) % (D / 3) == 0) return 0; }
  return 1; }
/* forbidden set: linear probing with backward-shift deletion */
#define FH (1 << 17)
static u64 fk[FH]; static char fu[FH];
static u64 hh(u64 k) { k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL; k ^= k >> 33; return k; }
static int fhas(u64 k) { u64 i = hh(k) & (FH - 1); while (fu[i]) { if (fk[i] == k) return 1; i = (i + 1) & (FH - 1); } return 0; }
static void fins(u64 k) { u64 i = hh(k) & (FH - 1); while (fu[i]) { if (fk[i] == k) return; i = (i + 1) & (FH - 1); } fu[i] = 1; fk[i] = k; }
static void fdel(u64 k) { u64 i = hh(k) & (FH - 1); while (fu[i] && fk[i] != k) i = (i + 1) & (FH - 1); if (!fu[i]) return;
  fu[i] = 0; u64 j = i;
  for (;;) { j = (j + 1) & (FH - 1); if (!fu[j]) break; u64 h = hh(fk[j]) & (FH - 1);
    if (i <= j ? (i < h && h <= j) : (i < h || h <= j)) continue;
    fk[i] = fk[j]; fu[i] = 1; fu[j] = 0; i = j; } }
/* solutions */
#define SH (1 << 22)
static u64 *sh; static long nsol = 0, nodes = 0;
static int shadd(u64 k) { u64 i = k & (SH - 1); while (sh[i]) { if (sh[i] == k) return 0; i = (i + 1) & (SH - 1); } sh[i] = k; return 1; }
static int nuD, uD[80];
static int cmpu(const void *a, const void *b) { u64 x = *(const u64 *)a, y = *(const u64 *)b; return x < y ? -1 : x > y; }
static El tr(const El *z, int t, const El *bs) {
  El o; o.s = (int)((ll)t * z->s % D);
  if (P) { o.u = mulm(z->u, invm(bs->u)); o.sg = 0; o.a = o.b = 0; }
  else { o.sg = z->sg * bs->sg; o.a = z->a - bs->a; o.b = z->b - bs->b; o.u = 0; }
  return o; }
static void record(void) {
  u64 best[8], cur[8]; El bestE[8], curE[8]; int first = 1;
  for (int i = 0; i < nS; i++) { int g = gS[S[i].s] % D;
    for (int q = 0; q < nuD; q++) { int t = uD[q]; if ((ll)t * S[i].s % D != g) continue;
      for (int j = 0; j < nS; j++) { curE[j] = tr(&S[j], t, &S[i]); }
      /* sort by key */
      for (int a = 1; a < nS; a++) for (int b = a; b > 0 && ekey(&curE[b]) < ekey(&curE[b - 1]); b--) { El tmp = curE[b]; curE[b] = curE[b - 1]; curE[b - 1] = tmp; }
      for (int j = 0; j < nS; j++) cur[j] = ekey(&curE[j]);
      int lt = first; if (!first) for (int j = 0; j < nS; j++) { if (cur[j] < best[j]) { lt = 1; break; } if (cur[j] > best[j]) break; }
      if (lt) { memcpy(best, cur, nS * 8); memcpy(bestE, curE, nS * sizeof(El)); first = 0; } } }
  u64 h = 1469598103934665603ULL; for (int j = 0; j < nS; j++) { h ^= best[j] + 7; h *= 1099511628211ULL; } h ^= nS; h |= 1;
  if (!shadd(h)) return;
  nsol++;
  if (P) { ll N = (ll)D * P, iD = invm(D % P); printf("C n=%d c=0 d=0 :", nS);
    for (int j = 0; j < nS; j++) { ll s = bestE[j].s, u = bestE[j].u; ll k = mulm(((u - s) % P + P) % P, iD); ll x = (s + (ll)D * k) % N;
      printf(" %lld/%lld", x, (ll)dS[s] * P); } }
  else { printf("F n=%d :", nS); for (int j = 0; j < nS; j++) printf(" %d,%d,%d,%d", bestE[j].s, bestE[j].sg, bestE[j].a, bestE[j].b); }
  printf("\n"); fflush(stdout); }
/* covers */
typedef struct { int s, al, be; } Cv;
static Cv covl[ML][1200]; static int ncovl[ML], maxpt[ML];
static void dfs(void) {
  nodes++;
  int best = -1, nz[ML] = {0};
  for (int i = 0; i < npts; i++) if (nonzero(&pts[i])) { nz[pts[i].L]++; if (best < 0 || ncovl[pts[i].L] < ncovl[pts[best].L]) best = i; }
  if (best < 0) { record(); return; }
  if (nS >= MAXN) return;
  int rem = MAXN - nS;
  for (int L = 0; L < nl; L++) if (nz[L]) { if (!maxpt[L]) return; if ((nz[L] + maxpt[L] - 1) / maxpt[L] > rem) return; }
  int L = pts[best].L; u64 key = pts[best].key;
  El cov[2400]; int nc = 0;
  for (int k = 0; k < ncovl[L]; k++) { const Cv *cv = &covl[L][k];
    for (int sg = -1; sg <= 1; sg += 2) { El y; y.s = cv->s;
      if (P) { ll vh = (ll)(key & ((1ULL << 56) - 1)); ll u = mulm(vh, pw23[cv->al][cv->be]); y.u = sg > 0 ? u : P - u; y.sg = y.a = y.b = 0; }
      else { int a = (int)((key >> 24) & ((1 << 24) - 1)) - (1 << 20), b = (int)(key & ((1 << 24) - 1)) - (1 << 20);
        y.sg = sg; y.a = a + cv->al; y.b = b + cv->be; y.u = 0; }
      if (fhas(ekey(&y)) || !okadd(&y)) continue;
      cov[nc++] = y; } }
  for (int i = 0; i < nc; i++) { int old = addel(&cov[i]); dfs(); delel(old); fins(ekey(&cov[i])); }
  for (int i = 0; i < nc; i++) fdel(ekey(&cov[i])); }
static int v2(int n) { int k = 0; while (n % 2 == 0) { n /= 2; k++; } return k; }
static int v3(int n) { int k = 0; while (n % 3 == 0) { n /= 3; k++; } return k; }
int main(int argc, char **argv) {
  V = atoi(argv[1]); W = atoi(argv[2]); P = atoll(argv[3]); if (argc > 4) MAXN = atoi(argv[4]);
  D = 1; for (int i = 0; i < V; i++) D *= 2; for (int i = 0; i < W; i++) D *= 3;
  if (P && P < 29) fprintf(stderr, "warning: p < 29, constants not treated\n");
  phiD = phi(D);
  for (int t = 1; t <= D; t++) if (gcdi(t, D) == 1) uD[nuD++] = t % D;
  if (P) for (int a = 0; a < 8; a++) for (int b = 0; b < 8; b++) { ll x = 1; for (int i = 0; i < a; i++) x = x * 2 % P; for (int i = 0; i < b; i++) x = x * 3 % P; pw23[a][b] = x; inv23[a][b] = invm(x); }
  for (int c = 1; c <= D; c++) { if (D % c || c % 4 == 2) continue; int L = nl++; lc[L] = c; lph[L] = 0;
    for (int r = 0; r < c; r++) { lix[L][r] = -1; if (gcdi(r, c) == 1 || c == 1) { lix[L][r] = lph[L]; lu[L][lph[L]++] = r; } }
    for (int j = 0; j < lph[L]; j++) { int vec[24] = {0}, nw[24]; vec[j] = 1;
      for (int l = 2; l <= 3; l++) { if (c % l) continue; int K[24], nK = 0;
        for (int k = 0; k < lph[L]; k++) if ((lu[L][k] - 1) % (c / l) == 0) K[nK++] = lu[L][k];
        for (int r = 0; r < lph[L]; r++) { int s = nK * vec[r]; for (int q = 0; q < nK; q++) s -= vec[lix[L][lu[L][r] * K[q] % c]]; nw[r] = s; }
        memcpy(vec, nw, sizeof nw); }
      for (int r = 0; r < lph[L]; r++) Pcol[L][j][r] = vec[r]; } }
  for (int s = 0; s < D; s++) { int g = gcdi(s, D), d = D / g, w = phiD / phi(d), sp = s / g; gS[s] = g; dS[s] = d; nent[s] = 0;
    for (int L = 0; L < nl; L++) { int c = lc[L]; if (d % c) continue; int ls[2], n = 0;
      for (int l = 2; l <= 3; l++) if (d % l == 0 && c % l) ls[n++] = l;
      for (int mask = 0; mask < (1 << n); mask++) { int pt = 1, sign = 1; for (int q = 0; q < n; q++) if (mask >> q & 1) { pt *= ls[q]; sign = -sign; }
        int r = 0; if (c > 1) { int ip = 0; for (int y = 1; y < c; y++) if (pt * y % c == 1) ip = y; r = sp % c * ip % c; }
        Ent *e = &ent[s][nent[s]++]; e->L = L; e->ri = lix[L][r]; e->al = v2(g) + v2(pt); e->be = v3(g) + v3(pt); e->m = sign * w; } } }
  sh = calloc(SH, sizeof(u64));
  for (int d0 = 1; d0 <= D; d0++) { if (D % d0) continue;
    for (int L = 0; L < nl; L++) { ncovl[L] = 0; maxpt[L] = 0; }
    for (int s = 0; s < D; s++) { if (dS[s] > d0) continue; int cnt[ML] = {0};
      for (int k = 0; k < nent[s]; k++) { Ent *e = &ent[s][k]; covl[e->L][ncovl[e->L]++] = (Cv){s, e->al, e->be}; cnt[e->L]++; }
      for (int L = 0; L < nl; L++) if (cnt[L] > maxpt[L]) maxpt[L] = cnt[L]; }
    El x0; x0.s = (D / d0) % D; x0.sg = 1; x0.a = x0.b = 0; x0.u = 1;
    long n0 = nodes, s0 = nsol;
    int old = addel(&x0); dfs(); delel(old);
    fprintf(stderr, "d0=%d nodes=%ld new=%ld\n", d0, nodes - n0, nsol - s0); }
  fprintf(stderr, "V=%d W=%d D=%d p=%lld maxn=%d solutions=%ld nodes=%ld\n", V, W, D, P, MAXN, nsol, nodes);
  return 0; }
