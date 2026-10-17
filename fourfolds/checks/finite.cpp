// Independent re-check in C++ of the finite arithmetic certified in
// lean/FermatFourfolds.lean.  Build: c++ -O2 -std=c++17 -o finite finite.cpp
#include <algorithm>
#include <cstdio>
#include <functional>
#include <numeric>
#include <set>
#include <vector>

using V = std::vector<int>;
static int fails = 0, total = 0;
static void check(const char *name, bool ok)
{
    ++total;
    if (!ok) { ++fails; std::printf("FAIL %s\n", name); }
}

static int md(long a, int M) { return (int)(((a % M) + M) % M); }
static int ord(int M, int y) { return M / std::gcd(md(y, M), M); }
static V mul(int M, int t, const V &A) { V r; for (int a : A) r.push_back(md((long)t * a, M)); return r; }
static V cat(V a, const V &b) { a.insert(a.end(), b.begin(), b.end()); return a; }
static std::multiset<int> ms(int M, const V &A) { std::multiset<int> s; for (int a : A) s.insert(md(a, M)); return s; }
static bool same(int M, const V &A, const V &B) { return ms(M, A) == ms(M, B); }

static std::vector<int> units(int M)
{
    std::vector<int> u;
    for (int t = 1; t < M; ++t) if (std::gcd(t, M) == 1) u.push_back(t);
    return u;
}

static bool balanced(int M, const V &A)
{
    long s = 0;
    for (int a : A) { if (md(a, M) == 0) return false; s += a; }
    if (s % M) return false;
    for (int t : units(M)) {
        long h = 0;
        for (int x : mul(M, t, A)) h += x;
        if (2 * h != (long)A.size() * M) return false;
    }
    return true;
}

static bool nopair(int M, const V &A)
{
    for (size_t i = 0; i < A.size(); ++i)
        for (size_t j = i + 1; j < A.size(); ++j)
            if (md(A[i] + A[j], M) == 0) return false;
    return true;
}

static V tee(int M, int x) { return {md(x, M), md(x + M / 2, M), md(-2L * x, M), M / 2}; }
static V sigma(int M, int l, int x)
{
    V r;
    for (int j = 0; j < l; ++j) r.push_back(md(x + (long)j * (M / l), M));
    r.push_back(md(-(long)l * x, M));
    return r;
}
static bool isprime(int p) { if (p < 2) return false; for (int d = 2; d * d <= p; ++d) if (p % d == 0) return false; return true; }

static std::vector<V> gens(int M)
{
    std::vector<V> G;
    for (int y = 1; y < M; ++y) G.push_back({y, md(-y, M)});
    for (int l = 3; l <= M; l += 2)
        if (isprime(l) && M % l == 0)
            for (int x = 0; x < M; ++x) if (md((long)l * x, M)) G.push_back(sigma(M, l, x));
    if (M % 2 == 0)
        for (int x = 0; x < M; ++x) if (md(2L * x, M)) G.push_back(tee(M, x));
    return G;
}

static bool vanishes(int M, const std::function<bool(int)> &nu)
{
    for (const V &A : gens(M))
        if (std::count_if(A.begin(), A.end(), nu) % 2) return false;
    return true;
}

static int angle(int m, int t, const V &a)
{
    long s = 0;
    for (int x : mul(m, t, a)) s += x;
    return s % m ? -1000 : (int)(s / m);
}

int main()
{
    // Section 2
    check("T(3)", tee(28, 3) == V{3, 17, 22, 14});
    check("sigma_{5,1}", sigma(20, 5, 1) == V{1, 5, 9, 13, 17, 15});
    check("move", balanced(28, {3, 5, 13, 17, 19, 27}) && balanced(28, {5, 6, 13, 14, 19, 27}) &&
                      same(28, {5, 13, 19, 27, md(-22, 28), md(-14, 28)}, {5, 6, 13, 14, 19, 27}));
    for (int M : {21, 28, 33, 35, 39, 44, 52, 66, 78, 102, 110, 114}) {
        bool ok = true;
        for (const V &G : gens(M)) ok = ok && balanced(M, G);
        check("standard balanced", ok);
    }

    // Section 4
    V O21{1, 4, 9, 15, 16, 18}, O33{1, 4, 16, 22, 25, 31}, O39{1, 7, 16, 22, 34, 37};
    check("orbits", balanced(21, O21) && balanced(33, O33) && balanced(39, O39));
    check("O21 id", same(21, cat(O21, {2, 19}), cat(sigma(21, 3, 2), {1, 4, 18, 19})) &&
                        balanced(21, {1, 4, 18, 19}));
    check("O33 id", same(66, cat(mul(66, 2, O33), {1, 65, 25, 41, 33, 33}),
                         cat(cat(V{1, 25, 44, 62}, tee(66, 32)), tee(66, 8))) &&
                        balanced(66, {1, 25, 44, 62}) && balanced(66, mul(66, 2, O33)));
    check("O39 id", same(78, cat(mul(78, 2, O39), {5, 73, 7, 71, 39, 39}),
                         cat(cat(V{2, 7, 73, 74}, tee(78, 32)), tee(78, 5))) &&
                        balanced(78, {2, 7, 73, 74}) && balanced(78, mul(78, 2, O39)));
    // units fixing the orbits, and coset representatives
    struct Orb { int M, q; V O, sq, reps; };
    for (const Orb &o : {Orb{21, 7, O21, {1, 2, 4}, {1, 2}}, Orb{33, 11, O33, {1, 3, 4, 5, 9}, {1, 5}},
                         Orb{39, 13, O39, {1, 3, 9}, {1, 2, 4, 8}}}) {
        bool inv = true, cov = true;
        for (int t : units(o.M)) {
            if (t % 3 == 1 && std::count(o.sq.begin(), o.sq.end(), t % o.q))
                inv = inv && same(o.M, mul(o.M, t, o.O), o.O);
            bool any = false;
            for (int s : o.reps)
                any = any || same(o.M, mul(o.M, t, o.O), mul(o.M, s, o.O)) ||
                      same(o.M, mul(o.M, t, o.O), mul(o.M, o.M - s, o.O));
            cov = cov && any;
        }
        check("orbit units", inv && cov);
    }

    // Section 5
    check("nu19", vanishes(114, [](int y) { return ord(114, y) == 19; }));
    check("nu17", vanishes(102, [](int y) { return ord(102, y) == 17; }));
    check("nu11", vanishes(44, [](int y) { return ord(44, y) == 11; }));
    check("nu13", vanishes(52, [](int y) { return ord(52, y) == 13; }));
    for (int M : {33, 35, 39}) check("nuR", vanishes(M, [M](int y) { return (long)y * y % M == 1; }));

    // Section 6
    struct Pair { int m; V a, b; int s; V beta; std::function<bool(int)> nu; int hit; };
    std::vector<Pair> pairs = {
        {114, {1, 25, 43, 57, 102}, {39, 63, 68, 80, 92}, 5, {1, 25, 39, 43, 57, 63, 68, 80, 92, 102},
         [](int y) { return ord(114, y) == 19; }, 102},
        {44, {1, 5, 8, 33, 41}, {9, 37, 42}, 4, {1, 5, 8, 9, 33, 37, 41, 42},
         [](int y) { return ord(44, y) == 11; }, 8},
        {52, {1, 5, 16, 37, 45}, {29, 18, 42, 50, 17}, 5, {1, 5, 16, 17, 18, 29, 37, 42, 45, 50},
         [](int y) { return ord(52, y) == 13; }, 16},
        {102, {1, 7, 51, 60, 85}, {91, 34, 26, 98, 57}, 5, {1, 7, 26, 34, 51, 57, 60, 85, 91, 98},
         [](int y) { return ord(102, y) == 17; }, 60},
        {35, {1, 2, 16, 21, 30}, {17, 22, 31}, 4, {1, 2, 16, 17, 21, 22, 30, 31},
         [](int y) { return (long)y * y % 35 == 1; }, 1}};
    for (const Pair &p : pairs) {
        bool ok = std::accumulate(p.a.begin(), p.a.end(), 0) % p.m == 0 &&
                  std::accumulate(p.b.begin(), p.b.end(), 0) % p.m == 0;
        for (int t : units(p.m)) ok = ok && angle(p.m, t, p.a) + angle(p.m, t, p.b) == p.s;
        ok = ok && same(p.m, cat(p.a, p.b), p.beta) && balanced(p.m, p.beta) && nopair(p.m, p.beta);
        V hits;
        for (int y : p.beta) if (p.nu(y)) hits.push_back(y);
        check("character pair", ok && hits == V{p.hit});
    }
    struct Pat { int m; V a; int D; std::vector<std::pair<V, int>> cols; };
    std::vector<Pat> pats = {
        {114, mul(114, 13, {39, 63, 68, 80, 92}), 3,
         {{{0, 0, 1, 2, 0}, 1}, {{0, 0, 2, 0, 1}, 1}, {{1, 3, 0, 0, 0}, 1}, {{2, 0, 0, 1, 2}, 1}}},
        {114, {1, 25, 43, 57, 102}, 24,
         {{{3, 1, 2, 0, 0}, 7}, {{0, 1, 5, 0, 1}, 2}, {{0, 0, 0, 2, 0}, 12}, {{1, 5, 0, 0, 1}, 3},
          {{0, 0, 0, 0, 19}, 1}}},
        {44, {1, 5, 8, 33, 41}, 11,
         {{{3, 0, 0, 0, 1}, 1}, {{0, 0, 11, 0, 0}, 1}, {{1, 1, 0, 0, 2}, 5}, {{1, 2, 0, 1, 0}, 3},
          {{0, 0, 0, 4, 0}, 2}}},
        {52, {1, 5, 16, 37, 45}, 14,
         {{{0, 0, 0, 3, 1}, 4}, {{0, 1, 1, 0, 3}, 1}, {{2, 1, 0, 0, 1}, 7}, {{0, 0, 13, 0, 0}, 1},
          {{0, 3, 0, 1, 0}, 2}}},
        {52, mul(52, 9, {29, 18, 42, 50, 17}), 5,
         {{{0, 0, 5, 1, 0}, 1}, {{3, 0, 0, 0, 1}, 1}, {{2, 0, 0, 3, 0}, 1}, {{0, 3, 0, 1, 0}, 1},
          {{0, 1, 0, 0, 2}, 2}}},
        {102, mul(102, 37, {91, 34, 26, 98, 57}), 6,
         {{{0, 0, 0, 3, 2}, 1}, {{0, 0, 3, 0, 4}, 1}, {{0, 3, 0, 0, 0}, 2}, {{2, 0, 1, 1, 0}, 3}}},
        {102, mul(102, 5, {1, 7, 51, 60, 85}), 18,
         {{{0, 0, 0, 0, 6}, 2}, {{0, 0, 0, 17, 0}, 1}, {{0, 0, 2, 0, 0}, 9}, {{0, 6, 0, 1, 0}, 1},
          {{3, 2, 0, 0, 1}, 6}}},
        {35, {1, 2, 16, 21, 30}, 50,
         {{{0, 0, 0, 5, 0}, 10}, {{1, 1, 2, 0, 0}, 25}, {{1, 2, 0, 0, 1}, 10}, {{3, 1, 0, 0, 1}, 5},
          {{0, 0, 0, 0, 35}, 1}}}};
    for (const Pat &p : pats) {
        bool ok = std::accumulate(p.a.begin(), p.a.end(), 0) % p.m == 0;
        for (int x : p.a) ok = ok && x % p.m;
        for (int k = 0; k < 5; ++k) {
            int c = 0;
            for (auto &col : p.cols) c += col.first[k] * col.second;
            ok = ok && c == p.D;
        }
        int sd = 0;
        for (auto &col : p.cols) {
            int w = 0;
            for (int k = 0; k < 5; ++k) w += col.first[k] * p.a[k];
            ok = ok && w % p.m == 0 && *std::max_element(col.first.begin(), col.first.end()) > 0 &&
                 *std::min_element(col.first.begin(), col.first.end()) == 0;
            sd += col.second;
        }
        check("block pattern", ok && sd == p.D + 1);
    }

    // Section 8
    {
        V A{1, 9, 16, 17, 20, 21};
        V T1 = tee(28, 1), T6 = tee(28, 6);
        V A1{9, 16, 17, 20, 21, md(-T1[1], 28), md(-T1[2], 28), md(-T1[3], 28)};
        V A2{2, 9, 13, 17, 21, md(-T6[0], 28)};
        check("chain at 28", balanced(28, A) && same(28, A1, {2, 9, 13, 14, 16, 17, 20, 21}) &&
                                 V{T6[1], T6[2], T6[3]} == V{20, 16, 14} &&
                                 same(28, A2, {2, 9, 17, 13, 21, 22}));
    }

    // Section 10 (small local configurations)
    for (auto r : std::vector<V>{{30, 1, 19, 25, 15}, {30, 1, 24, 20, 15}, {60, 1, 49, 40, 30}, {15, 1, 6, 13, 10},
                                 {20, 1, 12, 17, 10}, {30, 1, 7, 27, 25}, {60, 2, 21, 57, 40}, {28, 1, 9, 25, 21},
                                 {42, 1, 24, 38, 21}, {42, 1, 25, 37, 21}, {42, 1, 30, 32, 21}, {66, 1, 25, 62, 44},
                                 {78, 1, 55, 61, 39}})
        check("small completion", balanced(r[0], V(r.begin() + 1, r.end())));

    // Section 9 (level 110)
    {
        V A{19, 29, 39, 55, 79, 109};
        auto nu = [](int y) { return y % 10 == 4 || y % 10 == 5 || y % 10 == 6; };
        check("level 110", balanced(110, A) && nopair(110, A) && vanishes(110, nu) &&
                               std::count_if(A.begin(), A.end(), nu) % 2 == 1);
    }
    std::printf("%d checks passed, %d failed\n", total - fails, fails);
    return fails != 0;
}
