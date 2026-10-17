/* Enumerate level-one characters of the Fermat threefold X^3_M up to units
   and permutations.  Output: one line per orbit: entries, nu-count of
   elements of order L (given), and the type string over units t < M/2
   (1 if <t a> = 3, 0 if 2).
   usage: lev1 M L > file */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int cmp(const void *x, const void *y) { return *(int *)x - *(int *)y; }

int main(int argc, char **argv) {
  int M = atoi(argv[1]), L = atoi(argv[2]);
  int units[2000], nu = 0, half[2000], nh = 0;
  for (int t = 1; t < M; t++) if (gcd(t, M) == 1) { units[nu++] = t; if (2 * t < M) half[nh++] = t; }
  int a[5];
  long count = 0;
  for (a[0] = 1; a[0] < M; a[0]++)
  for (a[1] = a[0]; a[1] < M; a[1]++)
  for (a[2] = a[1]; a[2] < M; a[2]++)
  for (a[3] = a[2]; a[3] < M; a[3]++) {
    int s = a[0] + a[1] + a[2] + a[3];
    int a4 = (M - s % M) % M;
    if (a4 == 0 || a4 < a[3]) continue;
    a[4] = a4;
    /* level one */
    int ok = 1;
    char type[2000];
    for (int i = 0; i < nh && ok; i++) {
      int t = half[i], ss = 0;
      for (int k = 0; k < 5; k++) ss += (t * a[k]) % M;
      if (ss == 2 * M) type[i] = '0';
      else if (ss == 3 * M) type[i] = '1';
      else ok = 0;
    }
    if (!ok) continue;
    /* canonical: a is lexicographically least among sorted(t a) */
    for (int i = 0; i < nu && ok; i++) {
      int b[5];
      for (int k = 0; k < 5; k++) b[k] = (units[i] * a[k]) % M;
      qsort(b, 5, sizeof(int), cmp);
      for (int k = 0; k < 5; k++) {
        if (b[k] < a[k]) { ok = 0; break; }
        if (b[k] > a[k]) break;
      }
    }
    if (!ok) continue;
    type[nh] = 0;
    int nl = 0;
    for (int k = 0; k < 5; k++) { int o = M / gcd(a[k], M); if (o == L) nl++; }
    printf("%d %d %d %d %d %d %s\n", a[0], a[1], a[2], a[3], a[4], nl, type);
    count++;
  }
  fprintf(stderr, "M=%d orbits=%ld\n", M, count);
  return 0;
}
