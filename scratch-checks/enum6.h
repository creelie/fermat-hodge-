/* Enumerate the unit orbits of balanced sextuples at level M by meet in the
   middle on triples.  Each triple {a<=b<=c} gets a hash of (k_1,...,k_16),
   k_j = sum of the representatives of T_j*a, T_j*b, T_j*c for sixteen
   units T_j < M/2; two triples form a balanced sextuple only if their k
   add up to (3M,...,3M), so a triple is matched with the triples whose hash
   is that of the complementary vector (collisions are removed by the full
   balance test).  Calls visit(a) once per orbit with the sorted
   canonical representative (lexicographically least sorted multiple t*a).
   Requires globals M, units[], nu, half[], nh, a filter int pre6(const int*) (it must reject the multisets that contain a
   pair or are a union of two zero-sum triples, which are skipped early)
   applied before canonicalisation, and a function visit(const int*). */
#include <stdint.h>
typedef struct { uint64_t key; int a, b, c; } tri;
static int cmpi6(const void *x, const void *y) { return *(int *)x - *(int *)y; }
static int cmptri(const void *x, const void *y) { uint64_t p = ((const tri *)x)->key, q = ((const tri *)y)->key; return p < q ? -1 : p > q; }
static void canon6(const int *a, int *c) {
  int best[6], first = 1;
  for (int i = 0; i < nu; i++) { int b[6]; for (int k = 0; k < 6; k++) b[k] = (int)((long)units[i] * a[k] % M); qsort(b, 6, sizeof(int), cmpi6);
    if (first || memcmp(b, best, sizeof b) < 0) { int lt = first; if (!first) for (int k = 0; k < 6; k++) { if (b[k] < best[k]) { lt = 1; break; } if (b[k] > best[k]) break; } if (lt) { memcpy(best, b, sizeof b); first = 0; } } }
  memcpy(c, best, sizeof best);
}
static uint64_t *hs; static size_t hcap;
static uint64_t key6(const int *c) { uint64_t h = 1469598103934665603ULL; for (int k = 0; k < 6; k++) { h ^= (uint64_t)c[k]; h *= 1099511628211ULL; } return h | 1; }
static int hs_add(const int *c) { uint64_t k = key6(c); size_t i = k % hcap; while (hs[i]) { if (hs[i] == k) return 0; i = (i + 1) % hcap; } hs[i] = k; return 1; }
static void enum6(void (*visit)(const int *)) {
  int T[16], nt = nh < 16 ? nh : 16; for (int j = 0; j < nt; j++) T[j] = half[(long)j * nh / nt];
  long ntri = 0; for (int a = 1; a < M; a++) for (int b = a; b < M; b++) ntri += M - b;
  tri *tr = malloc(sizeof(tri) * ntri); uint64_t *cks = NULL; long n = 0;
  for (int a = 1; a < M; a++) for (int b = a; b < M; b++) for (int c = b; c < M; c++) {
    uint64_t h = 1469598103934665603ULL;
    for (int j = 0; j < nt; j++) { long k = (long)T[j] * a % M + (long)T[j] * b % M + (long)T[j] * c % M; h ^= (uint64_t)k; h *= 1099511628211ULL; }
    tr[n].key = h; tr[n].a = a; tr[n].b = b; tr[n].c = c; n++; }
  qsort(tr, n, sizeof(tri), cmptri);
  hcap = 1 << 22; hs = calloc(hcap, sizeof(uint64_t));
  for (long i = 0; i < n; i++) {
    { int a = tr[i].a, b = tr[i].b, c = tr[i].c; if ((a + b + c) % M == 0 || a + b == M || a + c == M || b + c == M) continue; }
    uint64_t key = tr[i].key, ck = 1469598103934665603ULL;
    for (int j = 0; j < nt; j++) { long k = (long)T[j] * tr[i].a % M + (long)T[j] * tr[i].b % M + (long)T[j] * tr[i].c % M; ck ^= (uint64_t)(3L * M - k); ck *= 1099511628211ULL; }
    if (ck < key) continue;  /* each unordered pair of triples once */
    long lo = 0, hi = n; while (lo < hi) { long md2 = (lo + hi) / 2; if (tr[md2].key < ck) lo = md2 + 1; else hi = md2; }
    for (long j = lo; j < n && tr[j].key == ck; j++) {
      if (ck == key && j < i) continue;
      int s[6] = {tr[i].a, tr[i].b, tr[i].c, tr[j].a, tr[j].b, tr[j].c};
      if (s[3] + s[4] == M || s[3] + s[5] == M || s[4] + s[5] == M) continue;
      long sum = 0; for (int k = 0; k < 6; k++) sum += s[k]; if (sum % M) continue;
      int ok = 1;
      for (int h = 0; h < nh && ok; h++) { long t = half[h], ss = 0; for (int k = 0; k < 6; k++) ss += t * s[k] % M; if (ss != 3L * M) ok = 0; }
      if (!ok) continue;
      if (!pre6(s)) continue;
      int c[6]; canon6(s, c); if (hs_add(c)) visit(c);
    }
  }
  (void)cks; free(tr); free(hs);
}
