# Independent re-check of the finite arithmetic certified in
# lean/FermatFourfolds.lean (same claims, written from scratch in Julia).

const counts = [0, 0]   # checks, failures

function check(name, cond::Bool)
    counts[1] += 1
    if !cond
        counts[2] += 1
        println("FAIL ", name)
    end
end

units(M) = [t for t in 1:M-1 if gcd(t, M) == 1]

function balanced(M, A)
    (mod(sum(A), M) != 0 || any(a -> mod(a, M) == 0, A)) && return false
    all(t -> 2 * sum(mod(t * a, M) for a in A) == length(A) * M, units(M))
end

order(M, y) = div(M, gcd(y, M))
neg(M, y) = mod(-y, M)
mul(M, t, A) = [mod(t * a, M) for a in A]
mseq(M, A, B) = sort(mod.(A, M)) == sort(mod.(B, M))
nopair(M, A) = all(mod(A[i] + A[j], M) != 0 for i in eachindex(A) for j in i+1:length(A))

function remove_all(A, S)
    A = copy(A)
    for s in S
        deleteat!(A, findfirst(==(s), A))
    end
    A
end

move(M, A, T, S) = vcat(remove_all(A, S), [neg(M, y) for y in remove_all(T, S)])
isprime(p) = p >= 2 && all(d -> p % d != 0, 2:isqrt(p))
oddprimes(M) = [l for l in 3:2:M if isprime(l) && M % l == 0]
phiset(M, l, x) = [mod(x + j * div(M, l), M) for j in 0:l-1]
sigma(M, l, x) = vcat(phiset(M, l, x), [neg(M, l * x)])
tee(M, x) = [mod(x, M), mod(x + div(M, 2), M), neg(M, 2 * x), div(M, 2)]

function gens(M)
    G = [[y, neg(M, y)] for y in 1:M-1]
    for l in oddprimes(M)
        append!(G, [sigma(M, l, x) for x in 0:M-1 if mod(l * x, M) != 0])
    end
    if iseven(M)
        append!(G, [tee(M, x) for x in 0:M-1 if mod(2 * x, M) != 0])
    end
    G
end

vanishes(M, nu) = all(G -> iseven(count(nu, G)), gens(M))

# Section 2
check("T(3) at 28", tee(28, 3) == [3, 17, 22, 14])
check("Phi_5(1) at 20", phiset(20, 5, 1) == [1, 5, 9, 13, 17] && neg(20, 5) == 15)
let A = [3, 5, 13, 17, 19, 27]
    check("move example", balanced(28, A) &&
          mseq(28, move(28, A, tee(28, 3), [3, 17]), [5, 6, 13, 14, 19, 27]) &&
          balanced(28, [5, 6, 13, 14, 19, 27]) &&
          [order(28, y) for y in (3, 17, 6, 14)] == [28, 28, 14, 2])
end
for M in (21, 28, 33, 35, 39, 44, 52, 66, 78, 102, 110, 114)
    check("standard balanced $M", all(G -> balanced(M, G), gens(M)))
end

# Section 4
const O21 = [1, 4, 9, 15, 16, 18]
const O33 = [1, 4, 16, 22, 25, 31]
const O39 = [1, 7, 16, 22, 34, 37]
check("O21 residues", mseq(21, O21,
      vcat([x for x in 0:20 if x % 3 == 1 && x % 7 in (1, 2, 4)], [9, 15, 18])))
check("O33 residues", mseq(33, O33,
      vcat([x for x in 0:32 if x % 3 == 1 && x % 11 in (1, 3, 4, 5, 9)], [22])))
check("O39 residues", mseq(39, O39,
      [x for x in 0:38 if x % 3 == 1 && x % 13 in (1, 3, 9, 7, 8, 11)]))
for (M, O, sq, reps, q) in ((21, O21, (1, 2, 4), (1, 2), 7), (33, O33, (1, 3, 4, 5, 9), (1, 5), 11),
                            (39, O39, (1, 3, 9), (1, 2, 4, 8), 13))
    check("invariance $M", all(mseq(M, mul(M, t, O), O)
                               for t in units(M) if t % 3 == 1 && t % q in sq))
    check("cosets $M", all(any(mseq(M, mul(M, t, O), mul(M, s, O)) ||
                               mseq(M, mul(M, t, O), [neg(M, y) for y in mul(M, s, O)])
                               for s in reps) for t in units(M)))
    check("balanced O$M", balanced(M, O) && sum(O) == 3 * M)
end
check("tO lists", mul(21, 2, O21) == [2, 8, 18, 9, 11, 15] &&
      mul(33, 5, O33) == [5, 20, 14, 11, 26, 23] && mul(39, 2, O39) == [2, 14, 32, 5, 29, 35] &&
      mul(39, 4, O39) == [4, 28, 25, 10, 19, 31] && mul(39, 8, O39) == [8, 17, 11, 20, 38, 23])
check("O21 identity", sigma(21, 3, 2) == [2, 9, 16, 15] &&
      mseq(21, vcat(O21, [2, 19]), vcat(sigma(21, 3, 2), [1, 4, 18, 19])) &&
      balanced(21, [1, 4, 18, 19]))
let a = mul(66, 2, O33)
    check("O33 identity", a == [2, 8, 32, 44, 50, 62] && mseq(66, tee(66, 32), [2, 32, 33, 65]) &&
          mseq(66, tee(66, 8), [8, 33, 41, 50]) &&
          mseq(66, vcat(a, [1, 65, 25, 41, 33, 33]), vcat([1, 25, 44, 62], tee(66, 32), tee(66, 8))) &&
          balanced(66, [1, 25, 44, 62]) && balanced(66, a))
end
let a = mul(78, 2, O39)
    check("O39 identity", a == [2, 14, 32, 44, 68, 74] && mseq(78, tee(78, 32), [14, 32, 39, 71]) &&
          mseq(78, tee(78, 5), [5, 39, 44, 68]) &&
          mseq(78, vcat(a, [5, 73, 7, 71, 39, 39]), vcat([2, 7, 73, 74], tee(78, 32), tee(78, 5))) &&
          balanced(78, [2, 7, 73, 74]) && balanced(78, a))
end
check("subsets mod 7", [[a, b, c] for a in 1:6 for b in a+1:6 for c in b+1:6 if (a + b + c) % 7 == 0] ==
      [[1, 2, 4], [3, 5, 6]])
let C = [sort(mul(13, 2^j, [1, 3, 9])) for j in 0:3]
    check("cosets mod 13", C == [[1, 3, 9], [2, 5, 6], [4, 10, 12], [7, 8, 11]] &&
          all(sort([neg(13, y) for y in C[j+1]]) == C[mod(j + 2, 4)+1] for j in 0:3))
end
check("residues mod 7, 11", Set(x * x % 7 for x in 1:6) == Set([1, 2, 4]) &&
      sort([3^j % 7 for j in 0:5]) == [1, 2, 3, 4, 5, 6] &&
      Set(3^j % 11 for j in 0:4) == Set(x * x % 11 for x in 1:10))

# Section 5
function Qset(M)
    out = Int[]
    for q in 2:M
        M % q != 0 && continue
        a = trailing_zeros(q)
        o = q >> a
        ps = oddprimes(o)
        if a in (0, 2) && all(o % (l * l) != 0 for l in ps) && iseven((a == 2) + length(ps))
            push!(out, q)
        end
    end
    out
end
check("Q sets", [Qset(M) for M in (114, 102, 44, 52, 33, 35, 39, 110, 1680)] ==
      [[57], [51], [44], [52], [33], [35], [39], [55], [12, 15, 20, 21, 28, 35, 420]])
for (M, l) in ((114, 19), (102, 17), (44, 11), (52, 13))
    check("nu_$l vanishes on S_$M", vanishes(M, y -> order(M, y) == l))
end
for M in (33, 35, 39)
    check("nu_R vanishes on S_$M", vanishes(M, y -> mod(y * y, M) == 1))
end

# Section 6
function angle(m, t, a)
    s = sum(mod(t * x, m) for x in a)
    @assert s % m == 0
    div(s, m)
end
halfunits(m) = [t for t in units(m) if 2 * t < m]

const PAIRS = [
    (114, [1, 25, 43, 57, 102], [39, 63, 68, 80, 92], 5, [1, 25, 39, 43, 57, 63, 68, 80, 92, 102],
     [2, 2, 2, 2, 3, 2, 2, 2, 3, 3, 2, 2, 3, 2, 2, 3, 3, 2],
     [3, 3, 3, 3, 2, 3, 3, 3, 2, 2, 3, 3, 2, 3, 3, 2, 2, 3], y -> order(114, y) == 19, [102]),
    (44, [1, 5, 8, 33, 41], [9, 37, 42], 4, [1, 5, 8, 9, 33, 37, 41, 42],
     [2, 2, 3, 2, 2, 2, 3, 3, 2, 3], [2, 2, 1, 2, 2, 2, 1, 1, 2, 1],
     y -> order(44, y) == 11, [8]),
    (52, [1, 5, 16, 37, 45], [29, 18, 42, 50, 17], 5, [1, 5, 16, 17, 18, 29, 37, 42, 45, 50],
     [2, 2, 2, 2, 3, 2, 3, 2, 3, 2, 2, 3], [3, 3, 3, 3, 2, 3, 2, 3, 2, 3, 3, 2],
     y -> order(52, y) == 13, [16]),
    (102, [1, 7, 51, 60, 85], [91, 34, 26, 98, 57], 5, [1, 7, 26, 34, 51, 57, 60, 85, 91, 98],
     [2, 2, 2, 2, 3, 2, 2, 3, 2, 2, 2, 3, 2, 3, 2, 3],
     [3, 3, 3, 3, 2, 3, 3, 2, 3, 3, 3, 2, 3, 2, 3, 2], y -> order(102, y) == 17, [60]),
    (35, [1, 2, 16, 21, 30], [17, 22, 31], 4, [1, 2, 16, 17, 21, 22, 30, 31],
     [2, 2, 2, 2, 2, 3, 2, 2, 2, 3, 3, 3], [2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1],
     y -> mod(y * y, 35) == 1, [1]),
]
for (m, a1, a2, s, beta, v1, v2, nu, hit) in PAIRS
    ok = all(x -> mod(x, m) != 0, vcat(a1, a2)) && mod(sum(a1), m) == 0 && mod(sum(a2), m) == 0
    ok = ok && all(t -> angle(m, t, a1) + angle(m, t, a2) == s, units(m))
    ok = ok && [angle(m, t, a1) for t in halfunits(m)] == v1
    ok = ok && [angle(m, t, a2) for t in halfunits(m)] == v2
    ok = ok && mseq(m, vcat(a1, a2), beta) && balanced(m, beta) && nopair(m, beta)
    ok = ok && filter(nu, beta) == hit
    check("character pair $m", ok)
end
check("order-l elements", [y for y in 0:113 if order(114, y) == 19] == collect(6:6:113) &&
      [y for y in 0:43 if order(44, y) == 11] == collect(4:4:43) &&
      [y for y in 0:51 if order(52, y) == 13] == collect(4:4:51) &&
      [y for y in 0:101 if order(102, y) == 17] == collect(6:6:101) &&
      [y for y in 0:34 if mod(y * y, 35) == 1] == [1, 6, 29, 34])
check("8 alpha at 35", mul(35, 8, [1, 2, 16, 21, 30]) == [8, 16, 23, 28, 30] &&
      mul(35, 8, [17, 22, 31]) == [31, 1, 3])

const PATTERNS = [
    (114, mul(114, 13, [39, 63, 68, 80, 92]), [51, 21, 86, 14, 56], 3,
     [((0, 0, 1, 2, 0), 1), ((0, 0, 2, 0, 1), 1), ((1, 3, 0, 0, 0), 1), ((2, 0, 0, 1, 2), 1)],
     [114, 228, 114, 228]),
    (114, [1, 25, 43, 57, 102], [1, 25, 43, 57, 102], 24,
     [((3, 1, 2, 0, 0), 7), ((0, 1, 5, 0, 1), 2), ((0, 0, 0, 2, 0), 12), ((1, 5, 0, 0, 1), 3),
      ((0, 0, 0, 0, 19), 1)], [114, 342, 114, 228, 1938]),
    (44, [1, 5, 8, 33, 41], [1, 5, 8, 33, 41], 11,
     [((3, 0, 0, 0, 1), 1), ((0, 0, 11, 0, 0), 1), ((1, 1, 0, 0, 2), 5), ((1, 2, 0, 1, 0), 3),
      ((0, 0, 0, 4, 0), 2)], [44, 88, 88, 44, 132]),
    (52, [1, 5, 16, 37, 45], [1, 5, 16, 37, 45], 14,
     [((0, 0, 0, 3, 1), 4), ((0, 1, 1, 0, 3), 1), ((2, 1, 0, 0, 1), 7), ((0, 0, 13, 0, 0), 1),
      ((0, 3, 0, 1, 0), 2)], [156, 156, 52, 208, 52]),
    (52, mul(52, 9, [29, 18, 42, 50, 17]), [1, 6, 14, 34, 49], 5,
     [((0, 0, 5, 1, 0), 1), ((3, 0, 0, 0, 1), 1), ((2, 0, 0, 3, 0), 1), ((0, 3, 0, 1, 0), 1),
      ((0, 1, 0, 0, 2), 2)], [104, 52, 104, 52, 104]),
    (102, mul(102, 37, [91, 34, 26, 98, 57]), [1, 34, 44, 56, 69], 6,
     [((0, 0, 0, 3, 2), 1), ((0, 0, 3, 0, 4), 1), ((0, 3, 0, 0, 0), 2), ((2, 0, 1, 1, 0), 3)],
     [306, 408, 102, 102]),
    (102, mul(102, 5, [1, 7, 51, 60, 85]), [5, 35, 51, 96, 17], 18,
     [((0, 0, 0, 0, 6), 2), ((0, 0, 0, 17, 0), 1), ((0, 0, 2, 0, 0), 9), ((0, 6, 0, 1, 0), 1),
      ((3, 2, 0, 0, 1), 6)], [102, 1632, 102, 306, 102]),
    (35, [1, 2, 16, 21, 30], [1, 2, 16, 21, 30], 50,
     [((0, 0, 0, 5, 0), 10), ((1, 1, 2, 0, 0), 25), ((1, 2, 0, 0, 1), 10), ((3, 1, 0, 0, 1), 5),
      ((0, 0, 0, 0, 35), 1)], [105, 35, 35, 35, 1050]),
]
for (m, a, stated, D, cols, w) in PATTERNS
    ok = a == stated && all(x -> mod(x, m) != 0, a) && mod(sum(a), m) == 0
    ok = ok && all(sum(e[k] * d for (e, d) in cols) == D for k in 1:5)
    ok = ok && all(maximum(e) > 0 && minimum(e) == 0 && d > 0 for (e, d) in cols)
    ww = [sum(e[k] * a[k] for k in 1:5) for (e, d) in cols]
    ok = ok && ww == w && all(x -> mod(x, m) == 0, ww)
    ok = ok && sum(d for (e, d) in cols) == D + 1
    check("block pattern $m $a", ok)
end
check("gcds", gcd(13, 114) == gcd(9, 52) == gcd(37, 102) == gcd(5, 102) == 1)
check("square roots 33 39", [y for y in 0:32 if mod(y * y, 33) == 1] == [1, 10, 23, 32] &&
      [y for y in 0:38 if mod(y * y, 39) == 1] == [1, 14, 25, 38] &&
      [y for y in O33 if mod(y * y, 33) == 1] == [1] && [y for y in O39 if mod(y * y, 39) == 1] == [1] &&
      nopair(33, O33) && nopair(39, O39))

# Section 8
tr(L, s) = [(a, b, c) for a in L for b in L for c in L if a <= b <= c && a + b + c == s]
check("M=20", tr([5, 10, 15], 30) == [(5, 10, 15), (10, 10, 10)] &&
      !nopair(20, [1, 17, 12, 5, 10, 15]) && !nopair(20, [1, 17, 12, 10, 10, 10]))
check("M=28 (b)", tr([7, 14, 21], 49) == [(7, 21, 21), (14, 14, 21)] &&
      !nopair(28, [1, 9, 25, 7, 21, 21]) && !nopair(28, [1, 9, 25, 14, 14, 21]))
let A = [1, 9, 16, 17, 20, 21]
    A1 = move(28, A, tee(28, 1), [1])
    A2 = move(28, A1, tee(28, 6), [20, 16, 14])
    check("M=28 (c)", balanced(28, A) && mseq(28, A1, [2, 9, 13, 14, 16, 17, 20, 21]) &&
          mseq(28, A2, [2, 9, 17, 13, 21, 22]) && (2 + 9 + 17) % 28 == 0 && (13 + 21 + 22) % 28 == 0)
end
check("M=44, 140", sum([1, 13, 37, 41, 5, 24]) == 121 && sum([7, 119, 84, 5, 45, 125]) == 385 &&
      sum([7, 119, 84, 55, 75, 115]) == 455)

# Section 9 (level 110)
let A110 = [19, 29, 39, 55, 79, 109], nu = y -> mod(y, 10) in (4, 5, 6)
    check("level 110", balanced(110, A110) && nopair(110, A110) && vanishes(110, nu) &&
          isodd(count(nu, A110)) && oddprimes(110) == [5, 11] &&
          iseven(count(y -> order(110, y) == 5, A110)) &&
          iseven(count(y -> order(110, y) == 11, A110)) && tee(110, 1) == [1, 56, 108, 55] &&
          [y for y in tee(110, 1) if mod(y * y, 110) == 1] == [1])
end

# Section 10 (small local configurations)
for (M, B) in ((30, [1, 19, 25, 15]), (30, [1, 24, 20, 15]), (60, [1, 49, 40, 30]),
               (15, [1, 6, 13, 10]), (20, [1, 12, 17, 10]), (30, [1, 7, 27, 25]),
               (60, [2, 21, 57, 40]), (28, [1, 9, 25, 21]), (42, [1, 24, 38, 21]),
               (42, [1, 25, 37, 21]), (42, [1, 30, 32, 21]), (66, [1, 25, 62, 44]),
               (78, [1, 55, 61, 39]))
    check("small completion $M $B", balanced(M, B))
end
check("small completions lower", all(order(M, y) < M for (M, y) in
      ((30, 25), (30, 15), (30, 20), (60, 40), (60, 30))) &&
      order(30, 1) == 30 && order(60, 1) == 60)

# Section 1
function factor(M)
    f = Dict{Int,Int}()
    d = 2
    while d * d <= M
        while M % d == 0
            f[d] = get(f, d, 0) + 1
            M = div(M, d)
        end
        d += 1
    end
    M > 1 && (f[M] = get(f, M, 0) + 1)
    f
end

function covered(M)
    f = factor(M)
    ps = Set(keys(f))
    M <= 100 || isodd(M) || (M <= 250 && !(M in (110, 114, 220, 228))) ||
        length(ps) == 1 || (get(f, 2, 0) == 1 && length(ps) == 2) ||
        (issubset(ps, Set([2, 3, 5, 7])) && M % 420 != 0) ||
        issubset(ps, Set([2, 3, 11])) || issubset(ps, Set([2, 3, 13])) ||
        ((issubset(ps, Set([2, 3, 17])) || issubset(ps, Set([2, 3, 19]))) && M % 4 != 0)
end

check("first open degrees", [M for M in 1:266 if M % 110 != 0 && !covered(M)] == [228, 258, 260, 266])

println("$(counts[1] - counts[2]) checks passed, $(counts[2]) failed")
exit(counts[2] == 0 ? 0 : 1)
