/* Independent re-check in C of the finite arithmetic certified in
   lean/FermatFourfolds.lean.  Build: cc -O2 -o finite finite.c */
#include <stdio.h>
#include <string.h>

static int fails = 0, count = 0;
static void check(const char *name, int ok)
{
	count++;
	if (!ok) {
		fails++;
		printf("FAIL %s\n", name);
	}
}

static int gcd(int a, int b) { while (b) { int r = a % b; a = b; b = r; } return a; }
static int ord(int M, int y) { return M / gcd(y % M, M); }
static int neg(int M, int y) { return ((M - y % M) % M); }

static int balanced(int M, const int *A, int n)
{
	int s = 0;
	for (int i = 0; i < n; i++) {
		if (A[i] % M == 0) return 0;
		s += A[i];
	}
	if (s % M) return 0;
	for (int t = 1; t < M; t++) {
		if (gcd(t, M) != 1) continue;
		long h = 0;
		for (int i = 0; i < n; i++) h += (long)t * A[i] % M;
		if (2 * h != (long)n * M) return 0;
	}
	return 1;
}

static int mseq(int M, const int *A, int n, const int *B, int m)
{
	int c[4096];
	if (n != m) return 0;
	memset(c, 0, sizeof(int) * M);
	for (int i = 0; i < n; i++) c[A[i] % M]++;
	for (int i = 0; i < m; i++) c[B[i] % M]--;
	for (int y = 0; y < M; y++) if (c[y]) return 0;
	return 1;
}

static int nopair(int M, const int *A, int n)
{
	for (int i = 0; i < n; i++)
		for (int j = i + 1; j < n; j++)
			if ((A[i] + A[j]) % M == 0) return 0;
	return 1;
}

static int isprime(int p)
{
	if (p < 2) return 0;
	for (int d = 2; d * d <= p; d++) if (p % d == 0) return 0;
	return 1;
}

static int tee(int M, int x, int *out)
{
	out[0] = x % M; out[1] = (x + M / 2) % M; out[2] = neg(M, 2 * x); out[3] = M / 2;
	return 4;
}

static int sigma(int M, int l, int x, int *out)
{
	for (int j = 0; j < l; j++) out[j] = (x + j * (M / l)) % M;
	out[l] = neg(M, l * x);
	return l + 1;
}

typedef int (*nu_t)(int M, int y);
static int nu_ord_l;
static int nu_ord(int M, int y) { return ord(M, y) == nu_ord_l; }
static int nu_sq(int M, int y) { return (long)y * y % M == 1; }
static int nu_110(int M, int y) { (void)M; return y % 10 == 4 || y % 10 == 5 || y % 10 == 6; }

static int count_nu(nu_t nu, int M, const int *A, int n)
{
	int c = 0;
	for (int i = 0; i < n; i++) c += nu(M, A[i]);
	return c;
}

/* checks that every generator of S_M is balanced, and that nu (if given)
   counts an even number of entries of each */
static int gens_ok(int M, nu_t nu)
{
	int G[256], n;
	for (int y = 1; y < M; y++) {
		G[0] = y; G[1] = neg(M, y);
		if (!balanced(M, G, 2)) return 0;
		if (nu && count_nu(nu, M, G, 2) % 2) return 0;
	}
	for (int l = 3; l <= M; l += 2) {
		if (!isprime(l) || M % l) continue;
		for (int x = 0; x < M; x++) {
			if (l * x % M == 0) continue;
			n = sigma(M, l, x, G);
			if (!balanced(M, G, n)) return 0;
			if (nu && count_nu(nu, M, G, n) % 2) return 0;
		}
	}
	if (M % 2 == 0)
		for (int x = 0; x < M; x++) {
			if (2 * x % M == 0) continue;
			n = tee(M, x, G);
			if (!balanced(M, G, n)) return 0;
			if (nu && count_nu(nu, M, G, n) % 2) return 0;
		}
	return 1;
}

static int angle(int m, int t, const int *a, int n)
{
	int s = 0;
	for (int i = 0; i < n; i++) s += t * a[i] % m;
	return s % m ? -1000 : s / m;
}

static void mul(int M, int t, const int *A, int n, int *out)
{
	for (int i = 0; i < n; i++) out[i] = t * A[i] % M;
}

static int eq(const int *A, const int *B, int n) { return memcmp(A, B, sizeof(int) * n) == 0; }

struct pair {
	int m, n1, n2, s, nb;
	int a1[5], a2[5], beta[10];
	int v1[18], v2[18], nv;
	int l; /* order for nu_l, or 0 for nu_R */
	int hit;
};

static const struct pair PAIRS[] = {
	{114, 5, 5, 5, 10, {1, 25, 43, 57, 102}, {39, 63, 68, 80, 92},
	 {1, 25, 39, 43, 57, 63, 68, 80, 92, 102},
	 {2, 2, 2, 2, 3, 2, 2, 2, 3, 3, 2, 2, 3, 2, 2, 3, 3, 2},
	 {3, 3, 3, 3, 2, 3, 3, 3, 2, 2, 3, 3, 2, 3, 3, 2, 2, 3}, 18, 19, 102},
	{44, 5, 3, 4, 8, {1, 5, 8, 33, 41}, {9, 37, 42}, {1, 5, 8, 9, 33, 37, 41, 42},
	 {2, 2, 3, 2, 2, 2, 3, 3, 2, 3}, {2, 2, 1, 2, 2, 2, 1, 1, 2, 1}, 10, 11, 8},
	{52, 5, 5, 5, 10, {1, 5, 16, 37, 45}, {29, 18, 42, 50, 17},
	 {1, 5, 16, 17, 18, 29, 37, 42, 45, 50},
	 {2, 2, 2, 2, 3, 2, 3, 2, 3, 2, 2, 3}, {3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2}, 12, 13, 16},
	{102, 5, 5, 5, 10, {1, 7, 51, 60, 85}, {91, 34, 26, 98, 57},
	 {1, 7, 26, 34, 51, 57, 60, 85, 91, 98},
	 {2, 2, 2, 2, 3, 2, 2, 3, 2, 2, 2, 3, 2, 3, 2, 3},
	 {3, 3, 3, 3, 2, 3, 3, 2, 3, 3, 3, 2, 3, 2, 3, 2}, 16, 17, 60},
	{35, 5, 3, 4, 8, {1, 2, 16, 21, 30}, {17, 22, 31}, {1, 2, 16, 17, 21, 22, 30, 31},
	 {2, 2, 2, 2, 2, 3, 2, 2, 2, 3, 3, 3}, {2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1}, 12, 0, 1},
};

struct pattern {
	int m, t; int base[5]; int a[5]; int D, nc;
	int e[5][5]; int d[5]; int w[5];
};

static const struct pattern PATS[] = {
	{114, 13, {39, 63, 68, 80, 92}, {51, 21, 86, 14, 56}, 3, 4,
	 {{0, 0, 1, 2, 0}, {0, 0, 2, 0, 1}, {1, 3, 0, 0, 0}, {2, 0, 0, 1, 2}}, {1, 1, 1, 1},
	 {114, 228, 114, 228}},
	{114, 1, {1, 25, 43, 57, 102}, {1, 25, 43, 57, 102}, 24, 5,
	 {{3, 1, 2, 0, 0}, {0, 1, 5, 0, 1}, {0, 0, 0, 2, 0}, {1, 5, 0, 0, 1}, {0, 0, 0, 0, 19}},
	 {7, 2, 12, 3, 1}, {114, 342, 114, 228, 1938}},
	{44, 1, {1, 5, 8, 33, 41}, {1, 5, 8, 33, 41}, 11, 5,
	 {{3, 0, 0, 0, 1}, {0, 0, 11, 0, 0}, {1, 1, 0, 0, 2}, {1, 2, 0, 1, 0}, {0, 0, 0, 4, 0}},
	 {1, 1, 5, 3, 2}, {44, 88, 88, 44, 132}},
	{52, 1, {1, 5, 16, 37, 45}, {1, 5, 16, 37, 45}, 14, 5,
	 {{0, 0, 0, 3, 1}, {0, 1, 1, 0, 3}, {2, 1, 0, 0, 1}, {0, 0, 13, 0, 0}, {0, 3, 0, 1, 0}},
	 {4, 1, 7, 1, 2}, {156, 156, 52, 208, 52}},
	{52, 9, {29, 18, 42, 50, 17}, {1, 6, 14, 34, 49}, 5, 5,
	 {{0, 0, 5, 1, 0}, {3, 0, 0, 0, 1}, {2, 0, 0, 3, 0}, {0, 3, 0, 1, 0}, {0, 1, 0, 0, 2}},
	 {1, 1, 1, 1, 2}, {104, 52, 104, 52, 104}},
	{102, 37, {91, 34, 26, 98, 57}, {1, 34, 44, 56, 69}, 6, 4,
	 {{0, 0, 0, 3, 2}, {0, 0, 3, 0, 4}, {0, 3, 0, 0, 0}, {2, 0, 1, 1, 0}}, {1, 1, 2, 3},
	 {306, 408, 102, 102}},
	{102, 5, {1, 7, 51, 60, 85}, {5, 35, 51, 96, 17}, 18, 5,
	 {{0, 0, 0, 0, 6}, {0, 0, 0, 17, 0}, {0, 0, 2, 0, 0}, {0, 6, 0, 1, 0}, {3, 2, 0, 0, 1}},
	 {2, 1, 9, 1, 6}, {102, 1632, 102, 306, 102}},
	{35, 1, {1, 2, 16, 21, 30}, {1, 2, 16, 21, 30}, 50, 5,
	 {{0, 0, 0, 5, 0}, {1, 1, 2, 0, 0}, {1, 2, 0, 0, 1}, {3, 1, 0, 0, 1}, {0, 0, 0, 0, 35}},
	 {10, 25, 10, 5, 1}, {105, 35, 35, 35, 1050}},
};

/* Section 1 */
static int strip(int M, const int *ps, int n)
{
	for (int i = 0; i < n; i++) while (M % ps[i] == 0) M /= ps[i];
	return M;
}
static int primepower(int M)
{
	if (M < 2) return 0;
	int p = 2;
	while (M % p) p++;
	while (M % p == 0) M /= p;
	return M == 1;
}
static int covered(int M)
{
	static const int p57[] = {2, 3, 5, 7}, p11[] = {2, 3, 11}, p13[] = {2, 3, 13},
		p17[] = {2, 3, 17}, p19[] = {2, 3, 19};
	if (M <= 100 || M % 2 == 1) return 1;
	if (M <= 250 && M != 110 && M != 114 && M != 220 && M != 228) return 1;
	if (primepower(M) || (M % 4 == 2 && primepower(M / 2))) return 1;
	if (strip(M, p57, 4) == 1 && M % 420) return 1;
	if (strip(M, p11, 3) == 1 || strip(M, p13, 3) == 1) return 1;
	if ((strip(M, p17, 3) == 1 || strip(M, p19, 3) == 1) && M % 4) return 1;
	return 0;
}

int main(void)
{
	int B[64], C[64], n;

	/* Section 2 */
	n = tee(28, 3, B);
	{ int e[] = {3, 17, 22, 14}; check("T(3) at 28", eq(B, e, 4)); }
	n = sigma(20, 5, 1, B);
	{ int e[] = {1, 5, 9, 13, 17, 15}; check("sigma_{5,1} at 20", eq(B, e, 6)); }
	{
		int A[] = {3, 5, 13, 17, 19, 27}, A2[] = {5, 6, 13, 14, 19, 27};
		check("move example", balanced(28, A, 6) && balanced(28, A2, 6) && ord(28, 6) == 14 &&
		      ord(28, 14) == 2 && ord(28, 3) == 28 && ord(28, 17) == 28);
		/* A - {3,17} + {-22,-14} */
		int R[] = {5, 13, 19, 27, neg(28, 22), neg(28, 14)};
		check("move result", mseq(28, R, 6, A2, 6));
	}
	{
		int Ms[] = {21, 28, 33, 35, 39, 44, 52, 66, 78, 102, 110, 114};
		for (int i = 0; i < 12; i++) check("standard balanced", gens_ok(Ms[i], 0));
	}

	/* Section 4 */
	int O21[] = {1, 4, 9, 15, 16, 18}, O33[] = {1, 4, 16, 22, 25, 31}, O39[] = {1, 7, 16, 22, 34, 37};
	check("O21", balanced(21, O21, 6));
	check("O33", balanced(33, O33, 6) && nopair(33, O33, 6));
	check("O39", balanced(39, O39, 6) && nopair(39, O39, 6));
	{
		int L[] = {2, 9, 16, 15, 1, 4, 18, 19}, R[] = {1, 4, 9, 15, 16, 18, 2, 19}, Q[] = {1, 4, 18, 19};
		n = sigma(21, 3, 2, B);
		int e[] = {2, 9, 16, 15};
		check("O21 identity", eq(B, e, 4) && mseq(21, L, 8, R, 8) && balanced(21, Q, 4));
	}
	{
		int a[6], L[12], R[12], Q[] = {1, 25, 44, 62};
		mul(66, 2, O33, 6, a);
		memcpy(L, a, sizeof a);
		int add[] = {1, 65, 25, 41, 33, 33};
		memcpy(L + 6, add, sizeof add);
		memcpy(R, Q, sizeof Q);
		tee(66, 32, R + 4); tee(66, 8, R + 8);
		check("O33 identity", mseq(66, L, 12, R, 12) && balanced(66, Q, 4) && balanced(66, a, 6));
	}
	{
		int a[6], L[12], R[12], Q[] = {2, 7, 73, 74};
		mul(78, 2, O39, 6, a);
		memcpy(L, a, sizeof a);
		int add[] = {5, 73, 7, 71, 39, 39};
		memcpy(L + 6, add, sizeof add);
		memcpy(R, Q, sizeof Q);
		tee(78, 32, R + 4); tee(78, 5, R + 8);
		check("O39 identity", mseq(78, L, 12, R, 12) && balanced(78, Q, 4) && balanced(78, a, 6));
	}
	{
		int c = 0, ok = 1;
		for (int a = 1; a < 7; a++)
			for (int b = a + 1; b < 7; b++)
				for (int d = b + 1; d < 7; d++)
					if ((a + b + d) % 7 == 0) {
						c++;
						ok &= (a == 1 && b == 2 && d == 4) || (a == 3 && b == 5 && d == 6);
					}
		check("subsets mod 7", c == 2 && ok);
	}

	/* Section 5 */
	{
		int Ms[] = {114, 102, 44, 52}, ls[] = {19, 17, 11, 13};
		for (int i = 0; i < 4; i++) {
			nu_ord_l = ls[i];
			check("nu_l on S_M", gens_ok(Ms[i], nu_ord));
		}
		int Ns[] = {33, 35, 39};
		for (int i = 0; i < 3; i++) check("nu_R on S_M", gens_ok(Ns[i], nu_sq));
	}

	/* Section 6 */
	for (int k = 0; k < 5; k++) {
		const struct pair *P = &PAIRS[k];
		int m = P->m, ok = 1, j = 0, hits = 0, hitv = -1, u[64];
		int s1 = 0, s2 = 0;
		for (int i = 0; i < P->n1; i++) s1 += P->a1[i];
		for (int i = 0; i < P->n2; i++) s2 += P->a2[i];
		ok &= s1 % m == 0 && s2 % m == 0;
		for (int t = 1; t < m; t++) {
			if (gcd(t, m) != 1) continue;
			ok &= angle(m, t, P->a1, P->n1) + angle(m, t, P->a2, P->n2) == P->s;
			if (2 * t < m) {
				ok &= j < P->nv && angle(m, t, P->a1, P->n1) == P->v1[j] &&
				      angle(m, t, P->a2, P->n2) == P->v2[j];
				j++;
			}
		}
		ok &= j == P->nv;
		memcpy(u, P->a1, sizeof(int) * P->n1);
		memcpy(u + P->n1, P->a2, sizeof(int) * P->n2);
		ok &= mseq(m, u, P->n1 + P->n2, P->beta, P->nb);
		ok &= balanced(m, P->beta, P->nb) && nopair(m, P->beta, P->nb);
		for (int i = 0; i < P->nb; i++) {
			int y = P->beta[i];
			if (P->l ? ord(m, y) == P->l : (long)y * y % m == 1) { hits++; hitv = y; }
		}
		ok &= hits == 1 && hitv == P->hit;
		check("character pair", ok);
	}
	for (int k = 0; k < 8; k++) {
		const struct pattern *P = &PATS[k];
		int m = P->m, ok = gcd(P->t, m) == 1, a[5], sd = 0, s = 0;
		mul(m, P->t, P->base, 5, a);
		ok &= eq(a, P->a, 5);
		for (int i = 0; i < 5; i++) { ok &= a[i] % m != 0; s += a[i]; }
		ok &= s % m == 0;
		for (int i = 0; i < 5; i++) {
			int c = 0;
			for (int l = 0; l < P->nc; l++) c += P->e[l][i] * P->d[l];
			ok &= c == P->D;
		}
		for (int l = 0; l < P->nc; l++) {
			int pos = 0, zero = 0, w = 0;
			for (int i = 0; i < 5; i++) {
				pos |= P->e[l][i] > 0; zero |= P->e[l][i] == 0; w += P->e[l][i] * a[i];
			}
			ok &= pos && zero && w == P->w[l] && w % m == 0 && P->d[l] > 0;
			sd += P->d[l];
		}
		ok &= sd == P->D + 1;
		check("block pattern", ok);
	}

	/* Section 8 */
	{
		int A[] = {1, 9, 16, 17, 20, 21}, T[4];
		tee(28, 1, T);
		int A1[] = {9, 16, 17, 20, 21, neg(28, T[1]), neg(28, T[2]), neg(28, T[3])};
		int E1[] = {2, 9, 13, 14, 16, 17, 20, 21};
		tee(28, 6, T);
		int A2[] = {2, 9, 13, 17, 21, neg(28, T[0])};
		int E2[] = {2, 9, 17, 13, 21, 22};
		check("M=28 chain", T[1] == 20 && T[2] == 16 && T[3] == 14 && balanced(28, A, 6) &&
		      mseq(28, A1, 8, E1, 8) && mseq(28, A2, 6, E2, 6) &&
		      (2 + 9 + 17) % 28 == 0 && (13 + 21 + 22) % 28 == 0);
		check("sums", 1 + 13 + 37 + 41 + 5 + 24 == 121 && 7 + 119 + 84 + 5 + 45 + 125 == 385 &&
		      7 + 119 + 84 + 55 + 75 + 115 == 455);
	}

	/* Section 9 */
	{
		static const int rows[13][5] = {
			{30, 1, 19, 25, 15}, {30, 1, 24, 20, 15}, {60, 1, 49, 40, 30}, {15, 1, 6, 13, 10},
			{20, 1, 12, 17, 10}, {30, 1, 7, 27, 25}, {60, 2, 21, 57, 40}, {28, 1, 9, 25, 21},
			{42, 1, 24, 38, 21}, {42, 1, 25, 37, 21}, {42, 1, 30, 32, 21}, {66, 1, 25, 62, 44},
			{78, 1, 55, 61, 39}};
		for (int i = 0; i < 13; i++) check("small completion", balanced(rows[i][0], rows[i] + 1, 4));
	}

	/* Section 10 */
	{
		int A[] = {19, 29, 39, 55, 79, 109}, c5 = 0, c11 = 0;
		for (int i = 0; i < 6; i++) { c5 += ord(110, A[i]) == 5; c11 += ord(110, A[i]) == 11; }
		tee(110, 1, C);
		int sq = 0;
		for (int i = 0; i < 4; i++) sq += C[i] * C[i] % 110 == 1;
		check("level 110", balanced(110, A, 6) && nopair(110, A, 6) && gens_ok(110, nu_110) &&
		      count_nu(nu_110, 110, A, 6) % 2 == 1 && c5 % 2 == 0 && c11 % 2 == 0 &&
		      C[0] == 1 && C[1] == 56 && C[2] == 108 && C[3] == 55 && sq == 1);
	}

	/* Section 1 */
	{
		int got[8], k = 0;
		for (int M = 1; M < 267; M++) if (M % 110 && !covered(M) && k < 8) got[k++] = M;
		check("first open degrees", k == 4 && got[0] == 228 && got[1] == 258 && got[2] == 260 &&
		      got[3] == 266);
	}
	(void)n;
	printf("%d checks passed, %d failed\n", count - fails, fails);
	return fails != 0;
}
