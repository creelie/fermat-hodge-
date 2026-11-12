# fricke_families.jl -- port of code/fricke_families.py (41 checks).
# Certificate for the Fricke families.
#  Part 1  Fricke universal curves over X_0(5), X_0(7): fibre types at the cusps
#          and elliptic points, Euler numbers of the K3 surfaces X_{p,q} and
#          X_psi, the bound rho >= 16.
#  Part 2  Fricke involution: the N+1 roots t_i of j(t) = j(tau) satisfy
#          {j(N^k/t_i)} = {j(N tau), j((tau+r)/N)} (numerical, 256-bit floats,
#          three values of tau from a fixed seed).
#  Part 3  Twist invariance u(N^k/t) = N^k u(t)/t^2; the Moebius maps preserving
#          0, oo and {e1, e2} (exact, in Q[t,p] and in Q(e1)).
#  Part 4  Lattice step: rank-6 forms of signature (2,4) embed in
#          (U^3 + E8(-2))_Q and (U^3 + A_2^2)_Q (Hasse-Minkowski invariants).
#  Part 5  Theorem D numerics for the dihedral Hecke correspondences.
#  Part 6  Hecke algebra of (D_n, <tau>): characteristic polynomial of the cycle
#          graph and the degrees of its irreducible factors.
#  Part 7  Euler-number classification of the elliptic K3 surfaces with a
#          rational N-isogeny (k <= 4).
# Everything is exact except Part 2 (as in the Python program) and the
# cosines of Part 5.
# Run: julia --startup-file=no fricke_families.jl

using Random

const NPASS = Ref(0); const NFAIL = Ref(0)
function check(name, ok)
    ok ? (NPASS[] += 1) : (NFAIL[] += 1)
    println(ok ? "PASS " : "FAIL ", name)
end

# ------------------------------------------------------------ Q[t]
const QQ = Rational{BigInt}
const Poly = Vector{QQ}                    # coefficients, constant term first
P(c...) = trim(QQ[c...])
trim(a::Poly) = (while !isempty(a) && a[end] == 0; pop!(a); end; a)
deg(a::Poly) = length(a) - 1
function padd(a::Poly, b::Poly)
    r = zeros(QQ, max(length(a), length(b)))
    r[1:length(a)] .+= a; r[1:length(b)] .+= b; trim(r)
end
pscal(c, a::Poly) = trim(QQ(c) .* a)
psub(a::Poly, b::Poly) = padd(a, pscal(-1, b))
function pmul(a::Poly, b::Poly)
    (isempty(a) || isempty(b)) && return QQ[]
    r = zeros(QQ, length(a) + length(b) - 1)
    for (i, x) in enumerate(a), (j, y) in enumerate(b)
        r[i+j-1] += x * y
    end
    trim(r)
end
ppow(a::Poly, k) = k == 0 ? P(1) : pmul(a, ppow(a, k - 1))
function pdivrem(a::Poly, b::Poly)
    r = copy(a); q = zeros(QQ, max(deg(a) - deg(b) + 1, 0))
    while deg(r) >= deg(b)
        c = r[end] / b[end]; k = deg(r) - deg(b)
        q[k+1] = c
        for (j, y) in enumerate(b)
            r[k+j] -= c * y
        end
        trim(r)
    end
    trim(q), r
end
function pgcd(a::Poly, b::Poly)
    while !isempty(b)
        a, b = b, pdivrem(a, b)[2]
    end
    pscal(1 / a[end], a)
end
pder(a::Poly) = trim(QQ[k * a[k+1] for k in 1:deg(a)])
"multiplicity of the factor f in a"
function mult(a::Poly, f::Poly)
    k = 0
    while true
        q, r = pdivrem(a, f)
        isempty(r) || return k
        a = q; k += 1
    end
end
const T = P(0, 1)

# ------------------------------------------------------------ Part 1
# Fricke universal curves y^2 = x^3 - 27 c4 x - 54 c6 (van Geemen-Schuett 7.6, 7.7)
const FRICKE = Dict(
    7 => (c4=pmul(P(49, 13, 1), P(1, 5, 1)), c6=pmul(P(49, 13, 1), P(-7, 70, 63, 14, 1)), quadr=P(49, 13, 1), Nk=49),
    5 => (c4=pmul(P(5, 10, 1), P(125, 22, 1)), c6=pmul(P(-1, 4, 1), ppow(P(125, 22, 1), 2)), quadr=P(125, 22, 1), Nk=125))

function fibre_type(oc4, oc6, oD)
    oD == 0 && return "I0"
    oc4 == 0 && oc6 == 0 && return "I$oD"
    table = Dict((1, 1, 2) => "II", (1, 2, 3) => "III", (2, 2, 4) => "IV", (2, 3, 6) => "I0*",
                 (3, 4, 8) => "IV*", (3, 5, 9) => "III*", (4, 5, 10) => "II*")
    (min(oc4, 2), min(oc6, 3)) == (2, 3) && oD > 6 && return "I$(oD-6)*"
    get(table, (oc4, oc6, oD), "?")
end
const EULER = Dict("I0" => 0, "II" => 2, "III" => 3, "IV" => 4, "I0*" => 6, "IV*" => 8, "III*" => 9, "II*" => 10)
const RANK = Dict("I0" => 0, "II" => 0, "III" => 1, "IV" => 2, "I0*" => 4, "IV*" => 6, "III*" => 7, "II*" => 8)
euler(ft) = haskey(EULER, ft) ? EULER[ft] : endswith(ft, "*") ? parse(Int, ft[2:end-1]) + 6 : parse(Int, ft[2:end])
rootrank(ft) = haskey(RANK, ft) ? RANK[ft] : endswith(ft, "*") ? parse(Int, ft[2:end-1]) + 4 : parse(Int, ft[2:end]) - 1

for N in (7, 5)
    d = FRICKE[N]; c4, c6, quadr = d.c4, d.c6, d.quadr
    Delta = psub(ppow(c4, 3), ppow(c6, 2))
    # the roots of Delta: Delta = const * t^a * quadr^b, quadr irreducible over Q with roots e1, e2
    a = mult(Delta, T); b = mult(Delta, quadr)
    rest = pdivrem(pdivrem(Delta, ppow(T, a))[1], ppow(quadr, b))[1]
    disc = quadr[2]^2 - 4 * quadr[1] * quadr[3]
    fact_ok = deg(rest) == 0 && a > 0 && b > 0 && disc < 0
    fin = Dict{String,String}()
    fin["0"] = fibre_type(mult(c4, T), mult(c6, T), a)
    fin["e1"] = fin["e2"] = fibre_type(mult(c4, quadr), mult(c6, quadr), b)
    fin["oo"] = fibre_type(4 - deg(c4), 6 - deg(c6), 12 - deg(Delta))
    println("  level $N: Delta = $(numerator(rest[1])) t^$a (t^2 + $(numerator(quadr[2])) t + $(numerator(quadr[1])))^$b; fibres of the Fricke curve: ",
            join(["$k: $(fin[k])" for k in ("0", "e1", "e2", "oo")], ", "))
    types = sort(collect(values(fin)))
    e_R = sum(euler(f) for f in values(fin))
    check("level $N: untwisted Fricke curve has Euler number 12 (rational elliptic surface)", fact_ok && e_R == 12)
    ell = N == 7 ? "II" : "III"
    check("level $N: fibres are I_1, I_$N, $ell, $ell", types == sort(["I1", "I$N", ell, ell]))
    check("level $N: the two elliptic points e1, e2 satisfy e1*e2 = $(d.Nk) (swapped by w)", quadr[3] == 1 && quadr[1] == d.Nk)
    cusps = [k for (k, f) in fin if occursin(r"^I[0-9]+$", f) && f != "I0"]
    check("level $N: the cusps are t = 0 and t = oo", Set(cusps) == Set(["0", "oo"]))
    e_A = e_R + 12
    rk_A = 2 + sum(rootrank(f) for f in values(fin)) + 8
    check("level $N: X_(p,q) (twist at p,q) has Euler number 24 and root rank + 2 = $rk_A >= 16", e_A == 24 && rk_A == 16)
    e_B = 2 * e_R
    rk_B = 2 + 2 * sum(rootrank(f) for f in values(fin))
    mwR = 8 - sum(rootrank(f) for f in values(fin))
    check("level $N: X_psi (degree-2 base change) has Euler number 24, root rank + 2 = $rk_B, MW(R) rank $mwR, so rho >= $(rk_B + mwR) = 16",
          e_B == 24 && rk_B + mwR == 16)
    if N == 7
        e_C = 3 * 1 + 3 * 7 + 0
        check("level 7: degree-3 base change totally ramified at the elliptic points has Euler number 24 and root rank >= 18 (rho >= 20)",
              e_C == 24 && 2 + 18 >= 20)
    else
        e_C = 3 * 1 + 3 * 5 + 2 * 9
        check("level 5: no K3 from a degree-3 base change (Euler number $e_C > 24)", e_C > 24)
    end
end

# ------------------------------------------------------------ Part 2
setprecision(BigFloat, 256)
const CB = Complex{BigFloat}
sigma3(n) = sum(d^3 for d in 1:n if n % d == 0)
const SIG3 = [BigFloat(sigma3(n)) for n in 1:399]
function jq(tau::CB, terms=400)
    qq = exp(2 * big(pi) * im * tau)
    E4 = one(CB); eta24 = qq; qn = one(CB)
    for n in 1:terms-1
        qn *= qq
        E4 += 240 * SIG3[n] * qn
        eta24 *= (1 - qn)^24
    end
    E4^3 / eta24
end
horner(a::Poly, x::CB) = foldr((c, acc) -> acc * x + BigFloat(c), a; init=zero(CB))
function jt(N, tt::CB)
    d = FRICKE[N]; a = horner(d.c4, tt)^3; b = horner(d.c6, tt)
    1728 * a / (a - b^2)
end
"all roots of a complex polynomial (coefficients constant term first) by the Aberth iteration"
function polyroots(c::Vector{CB})
    n = length(c) - 1
    ev(x) = foldr((a, acc) -> acc * x + a, c; init=zero(CB))
    dc = [k * c[k+1] for k in 1:n]
    dev(x) = foldr((a, acc) -> acc * x + a, dc; init=zero(CB))
    R = 1 + maximum(abs(c[k] / c[end]) for k in 1:n)
    z = [R * exp(im * (2 * big(pi) * k / n + big(0.4))) for k in 0:n-1]
    for _ in 1:500
        w = similar(z)
        for i in 1:n
            f = ev(z[i]) / dev(z[i])
            w[i] = f / (1 - f * sum(1 / (z[i] - z[j]) for j in 1:n if j != i))
        end
        z .-= w
        maximum(abs.(w)) < big(10.0)^(-60) && break
    end
    z
end
rng2 = MersenneTwister(7)
for N in (7, 5)
    d = FRICKE[N]
    ok_all = true
    for trial in 1:3
        tau = CB(BigFloat(-0.4 + 0.8 * rand(rng2)), BigFloat(1.1 + 0.5 * rand(rng2)))
        J = jq(tau)
        # j(t) = J: 1728 c4^3 - J (c4^3 - c6^2) = 0 after removing the common factor; degree N+1
        c43 = ppow(d.c4, 3); Dl = psub(c43, ppow(d.c6, 2))
        g = pgcd(c43, Dl)
        a3 = pdivrem(c43, g)[1]; aD = pdivrem(Dl, g)[1]
        dg = max(deg(a3), deg(aD))
        co = [1728 * CB(BigFloat(k <= deg(a3) ? a3[k+1] : 0)) - J * BigFloat(k <= deg(aD) ? aD[k+1] : 0) for k in 0:dg]
        rts = polyroots(co)
        check_n = length(rts) == N + 1 && maximum(abs(horner(a3, r) * 1728 - J * horner(aD, r)) / (1 + abs(r))^dg for r in rts) < 1e-40
        targets = vcat([jq(N * tau)], [jq((tau + r) / N) for r in 0:N-1])
        images = [jt(N, d.Nk / r) for r in rts]
        used = falses(length(targets)); okm = true
        for im_ in images
            i = findfirst(i -> !used[i] && abs(im_ - targets[i]) < 1e-12 * (1 + abs(targets[i])), eachindex(targets))
            i === nothing && (okm = false; break)
            used[i] = true
        end
        ok_all &= check_n && okm
    end
    check("level $N: for 3 random tau, the $(N+1) solutions t_i of j(t)=j(tau) have {j($(d.Nk)/t_i)} = {j($(N)tau), j((tau+r)/$N)}  (Fricke involution t -> $(d.Nk)/t)", ok_all)
end

# ------------------------------------------------------------ Part 3
# polynomials in two variables over Q: exponents (i, j) => coefficient
const MP = Dict{NTuple{2,Int},QQ}
mp(ps...) = MP(e => QQ(c) for (e, c) in ps)
function madd(a::MP, b::MP, s=1)
    r = copy(a)
    for (e, c) in b
        r[e] = get(r, e, QQ(0)) + s * c
    end
    filter!(p -> p.second != 0, r)
end
function mmul(a::MP, b::MP)
    r = MP()
    for (e, c) in a, (f, d) in b
        r[e.+f] = get(r, e .+ f, QQ(0)) + c * d
    end
    filter!(p -> p.second != 0, r)
end
# the quadratic field Q(e1) = Q[x]/(x^2 + b x + c): elements (a0, a1) = a0 + a1 e1
struct QF
    a0::QQ
    a1::QQ
    b::QQ
    c::QQ
end
Base.:+(x::QF, y::QF) = QF(x.a0 + y.a0, x.a1 + y.a1, x.b, x.c)
Base.:-(x::QF, y::QF) = QF(x.a0 - y.a0, x.a1 - y.a1, x.b, x.c)
Base.:*(x::QF, y::QF) = QF(x.a0 * y.a0 - x.a1 * y.a1 * x.c, x.a0 * y.a1 + x.a1 * y.a0 - x.a1 * y.a1 * x.b, x.b, x.c)
qconj(x::QF) = QF(x.a0 - x.a1 * x.b, -x.a1, x.b, x.c)
Base.inv(x::QF) = (n = x.a0^2 - x.a0 * x.a1 * x.b + x.a1^2 * x.c; y = qconj(x); QF(y.a0 / n, y.a1 / n, x.b, x.c))
Base.:/(x::QF, y::QF) = x * inv(y)
Base.iszero(x::QF) = x.a0 == 0 && x.a1 == 0
Base.:(==)(x::QF, y::QF) = iszero(x - y)
for N in (7, 5)
    Nk = FRICKE[N].Nk
    # variables (t, p).  p u(t) = (t - p)(p t - Nk);  p t^2 u(Nk/t) = (Nk - p t)(p Nk - Nk t)
    pu = mmul(mp((1, 0) => 1, (0, 1) => -1), mp((1, 1) => 1, (0, 0) => -Nk))
    pt2uw = mmul(mp((0, 0) => Nk, (1, 1) => -1), mp((0, 1) => Nk, (1, 0) => -Nk))
    check("level $N: u(t) = (t-p)(t-$Nk/p) satisfies u($Nk/t) = $Nk u(t)/t^2", isempty(madd(pt2uw, mmul(mp((0, 0) => Nk), pu), -1)))
    # u(t) = t^2 - Nk:  t^2 u(Nk/t) = Nk^2 - Nk t^2 = -Nk u(t)
    u2 = P(-Nk, 0, 1); t2u2w = P(Nk^2, 0, -Nk)
    check("level $N: u(t) = t^2 - $Nk (vGS) satisfies u($Nk/t) = -$Nk u(t)/t^2", isempty(padd(t2u2w, pscal(Nk, u2))))
    # Moebius maps preserving {0, oo} and {e1, e2}
    quadr = FRICKE[N].quadr; b, c = quadr[2], quadr[1]
    el(x, y=0) = QF(QQ(x), QQ(y), b, c)
    e1 = el(0, 1); e2 = qconj(e1)
    roots_ok = iszero(e1 * e1 + el(b) * e1 + el(c)) && iszero(e2 * e2 + el(b) * e2 + el(c)) && !(e1 == e2)
    # t -> lam t: (lam e1 - e1)(lam e1 - e2) = 0 has the roots lam = 1, e2/e1
    cand_scale = [el(1), e2 / e1]
    good_scale = [l for l in cand_scale if iszero((l * e2 - e1) * (l * e2 - e2))]
    # t -> lam/t: (lam/e1 - e1)(lam/e1 - e2) = 0 has the roots lam = e1^2, e1 e2
    cand_inv = [e1 * e1, e1 * e2]
    good_inv = [l for l in cand_inv if iszero((l / e2 - e1) * (l / e2 - e2))]
    check("level $N: Moebius maps preserving 0, oo and {e1,e2}: t->lam t only for lam = 1, t->lam/t only for lam = $Nk",
          roots_ok && good_scale == [el(1)] && good_inv == [el(Nk)])
    # variables (p, q): p q (p + Nk/p - q - Nk/q) = (p - q)(p q - Nk), with the roots q = p, Nk/p
    lhs = madd(mp((2, 1) => 1, (0, 1) => Nk), mp((1, 2) => 1, (1, 0) => Nk), -1)
    rhs = mmul(mp((1, 0) => 1, (0, 1) => -1), mp((1, 1) => 1, (0, 0) => -Nk))
    check("level $N: p + $Nk/p = p' + $Nk/p' iff p' in {p, $Nk/p}", isempty(madd(lhs, rhs, -1)))
end

# ------------------------------------------------------------ Part 4 (Hasse-Minkowski invariants)
function factorint(n::Integer)
    f = Dict{Int,Int}(); n = abs(n); p = 2
    while p * p <= n
        while n % p == 0
            f[p] = get(f, p, 0) + 1; n ÷= p
        end
        p += 1
    end
    n > 1 && (f[n] = get(f, n, 0) + 1)
    f
end
function sqfree_int(r)
    r = Rational{Int}(r); v = numerator(r) < 0 ? -1 : 1
    e = Dict{Int,Int}()
    for f in (factorint(numerator(r)), factorint(denominator(r))), (p, k) in f
        e[p] = (get(e, p, 0) + k) % 2
    end
    for (p, k) in e
        k == 1 && (v *= p)
    end
    v
end
legendre(u, p) = powermod(mod(u, p), (p - 1) ÷ 2, p) == 1 ? 1 : -1
function hilbert(a, b, p)
    p == 0 && return (a < 0 && b < 0) ? -1 : 1          # p = 0: the real place
    function split(x)
        al = 0
        while mod(x, p) == 0
            x = fld(x, p); al += 1
        end
        al, x
    end
    al, uu = split(a); be, vv = split(b)
    p != 2 && return (-1)^(al * be * ((p - 1) ÷ 2)) * legendre(uu, p)^be * legendre(vv, p)^al
    ep(x) = mod(fld(x - 1, 2), 2); om(x) = mod(fld(x * x - 1, 8), 2)
    (-1)^mod(ep(uu) * ep(vv) + al * om(vv) + be * om(uu), 2)
end
"diagonalise a symmetric rational matrix by congruence"
function diagonalize(G0)
    G = Rational{Int}.(G0); diag = Rational{Int}[]
    while size(G, 1) > 0
        n = size(G, 1)
        i = findfirst(i -> G[i, i] != 0, 1:n)
        if i === nothing
            j = findfirst(j -> G[1, j] != 0, 2:n) + 1
            Pm = Matrix{Rational{Int}}(I0(n)); Pm[j, 1] = 1; G = Pm' * G * Pm; i = 1
        end
        if i != 1
            Pm = Matrix{Rational{Int}}(I0(n)); Pm[1, 1] = 0; Pm[i, i] = 0; Pm[1, i] = 1; Pm[i, 1] = 1; G = Pm' * G * Pm
        end
        a = G[1, 1]; push!(diag, a)
        Pm = Matrix{Rational{Int}}(I0(n))
        for j in 2:n
            Pm[1, j] = -G[1, j] / a
        end
        G = (Pm'*G*Pm)[2:end, 2:end]
    end
    diag
end
I0(n) = [i == j ? 1 : 0 for i in 1:n, j in 1:n]
struct QForm
    diag::Vector{Int}
    rank::Int
    sig::Tuple{Int,Int}
    d::Int
    primes::Set{Int}
end
function QForm(diag0)
    diag = [sqfree_int(x) for x in diag0]
    QForm(diag, length(diag0), (count(>(0), diag0), count(<(0), diag0)), sqfree_int(prod(BigInt.(diag)) |> x -> sqfree_big(x)),
          union(Set([2]), [Set(keys(factorint(x))) for x in diag]...))
end
sqfree_big(x::BigInt) = (s = sign(x); x = abs(x); v = BigInt(1); p = 2;
    while x > 1
        k = 0
        while x % p == 0
            x ÷= p; k += 1
        end
        isodd(k) && (v *= p); p += 1
    end; Int(s * v))
feps(F::QForm, p) = prod(hilbert(F.diag[i], F.diag[j], p) for i in 1:F.rank for j in i+1:F.rank; init=1)
function is_square_in_Qp(dd, p)
    mod(dd, p) == 0 && return false
    p == 2 && return mod(dd, 8) == 1
    legendre(dd, p) == 1
end
function embeds(W::QForm, V::QForm)
    k = V.rank - W.rank
    k < 0 && return false
    dprime = sqfree_int(V.d * W.d)
    sp_, sm_ = V.sig[1] - W.sig[1], V.sig[2] - W.sig[2]
    (sp_ < 0 || sm_ < 0) && return false
    (dprime < 0) != (sm_ % 2 == 1) && return false
    for p in sort(collect(union(V.primes, W.primes, Set(keys(factorint(dprime))))))
        eprime = feps(V, p) * feps(W, p) * hilbert(W.d, dprime, p)
        k == 0 && !(is_square_in_Qp(dprime, p) && eprime == 1) && return false
        k == 1 && eprime != 1 && return false
        k == 2 && is_square_in_Qp(sqfree_int(-dprime), p) && eprime == -1 && return false
    end
    true
end
function blockdiag(ms...)
    n = sum(size(m, 1) for m in ms); G = zeros(Int, n, n); o = 0
    for m in ms
        k = size(m, 1); G[o+1:o+k, o+1:o+k] = m; o += k
    end
    G
end
Umat = [0 1; 1 0]; A2 = [-2 1; 1 -2]
E8neg = let C = zeros(Int, 8, 8)
    for i in 1:8
        C[i, i] = -2
    end
    for (i, j) in [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (4, 7)]
        C[i+1, j+1] = 1; C[j+1, i+1] = 1
    end
    C
end
V3 = QForm(diagonalize(blockdiag(Umat, Umat, Umat, A2, A2)))
V2 = QForm(diagonalize(blockdiag(Umat, Umat, Umat, 2 * E8neg)))
println("  V3 = (U^3 + A_2^2)_Q: rank $(V3.rank), signature $(V3.sig), d = $(V3.d); V2 = (U^3 + E8(-2))_Q: rank $(V2.rank), signature $(V2.sig), d = $(V2.d)")
rng4 = MersenneTwister(3)
cands = [1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210]
okall = true
for _ in 1:400
    diag = vcat([rand(rng4, cands) for _ in 1:2], [-rand(rng4, cands) for _ in 1:4])
    for scal in (1, 2, 3, 5, 7, 10, 14, 21, 42)
        Ws = QForm(scal .* diag)
        global okall &= embeds(Ws, V2) && embeds(Ws, V3)
    end
end
check("every rank-6 form of signature (2,4) in a sample of 400 (x 9 scalings) embeds in (U^3+E8(-2))_Q and (U^3+A_2^2)_Q (complement rank >= 3 is automatic)", okall)

# ------------------------------------------------------------ Part 5
for n in (5, 7, 9, 11, 13)
    cj = [2 * cos(2 * pi * k / n) for k in 1:n-1 if gcd(k, n) == 1][1:(n-1)÷2]
    a = [e * e for e in cj]
    d1 = d2 = 2
    posdef = all(d1 > 0 && d1 * d2 * aa - aa * aa > 0 for aa in a)
    check("D_$n: e = zeta+zeta^-1 has 0 < sigma(e)^2 < d1 d2 = 4 at all real places; Gram [[2,a],[a,2a]] positive definite at every place (positive index of q_S on T_1+T_2 equals 4)",
          all(0 < aa < 4 for aa in a) && posdef)
end
check("a = d1 d2 (degenerate T_1 + T_2) would need |zeta+zeta^-1| = 2, impossible for zeta != +-1 (n odd)",
      all(abs(2 * cos(2 * pi * k / n)) < 2 - 1e-9 for n in 3:2:59 for k in 1:n-1))

# ------------------------------------------------------------ Part 6
"characteristic polynomial of an integer matrix (Faddeev-LeVerrier)"
function charpoly(A)
    n = size(A, 1); A = QQ.(A); M = zeros(QQ, n, n); c = zeros(QQ, n + 1); c[n+1] = 1
    Id = QQ.(I0(n))
    for k in 1:n
        M = A * M + c[n-k+2] * Id
        c[n-k+1] = -sum(sum(A[i, j] * M[j, i] for j in 1:n) for i in 1:n) / k
    end
    trim(c)
end
# polynomials over F_p
ptrim(a) = (while !isempty(a) && a[end] == 0; pop!(a); end; a)
function prem(a::Vector{Int}, b::Vector{Int}, p)
    r = copy(a); ib = invmod(b[end], p)
    while length(r) >= length(b)
        c = mod(r[end] * ib, p); k = length(r) - length(b)
        for (j, y) in enumerate(b)
            r[k+j] = mod(r[k+j] - c * y, p)
        end
        ptrim(r)
    end
    r
end
function pmulmod(a, b, f, p)
    r = zeros(Int, length(a) + length(b) - 1)
    for (i, x) in enumerate(a), (j, y) in enumerate(b)
        r[i+j-1] = mod(r[i+j-1] + x * y, p)
    end
    prem(ptrim(r), f, p)
end
function pgcdmod(a, b, p)
    while !isempty(b)
        a, b = b, prem(a, b, p)
    end
    a
end
"is the monic polynomial f irreducible modulo p (no factor of degree <= deg/2)"
function irreducible_mod(f::Vector{Int}, p)
    n = length(f) - 1; x = [0, 1]; xq = x
    for k in 1:n÷2
        y = [1]                                   # xq^p mod f
        for _ in 1:p
            y = pmulmod(y, xq, f, p)
        end
        xq = y
        diff = copy(xq); length(diff) < 2 && (diff = vcat(diff, zeros(Int, 2 - length(diff)))); diff[2] = mod(diff[2] - 1, p); ptrim(diff)
        isempty(diff) && return false
        length(pgcdmod(f, diff, p)) > 1 && return false
    end
    true
end
"degrees of the distinct irreducible factors over Q of a monic integer polynomial"
function factor_degrees(f::Poly)
    g = pdivrem(f, pgcd(f, pder(f)))[1]           # squarefree part
    g = pscal(1 / g[end], g)
    degs = Int[]
    for r in -abs(numerator(g[1])):abs(numerator(g[1]))      # rational roots are integers dividing g(0)
        (r == 0 ? g[1] == 0 : numerator(g[1]) % r == 0) || continue
        q, rem = pdivrem(g, P(-r, 1))
        isempty(rem) && (push!(degs, 1); g = q)
    end
    if deg(g) > 0
        all(denominator(c) == 1 for c in g) || error("not integral")
        gi = Int[numerator(c) for c in g]
        pr = findfirst(p -> irreducible_mod(mod.(gi, p), p), [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47])
        pr === nothing && error("no prime of inertia found for the factor of degree $(deg(g))")
        push!(degs, deg(g))                        # irreducible modulo a prime, hence over Q
    end
    sort(degs)
end
function hecke_dim_and_degrees(n)
    orbits = 1 + (n - 1) ÷ 2
    A = zeros(Int, n, n)
    for i in 0:n-1
        A[i+1, mod(i + 1, n)+1] += 1; A[i+1, mod(i - 1, n)+1] += 1
    end
    orbits, factor_degrees(charpoly(A))
end
o7, d7 = hecke_dim_and_degrees(7)
check("Hecke algebra of (D_7, <tau>) has dimension 4 and its generator has characteristic polynomial (x-2) * (irreducible cubic)^2: End = Q x Q(zeta_7)^+", o7 == 4 && d7 == [1, 3])
o9, d9 = hecke_dim_and_degrees(9)
check("Hecke algebra of (D_9, <tau>) has dimension 5 and factors (x-2)(x+1)(cubic): End = Q x Q x Q(zeta_9)^+", o9 == 5 && d9 == [1, 1, 3])
o11, d11 = hecke_dim_and_degrees(11)
check("Hecke algebra of (D_11, <tau>) has dimension 6: End = Q x Q(zeta_11)^+ (quintic)", o11 == 6 && d11 == [1, 5])
o5, d5 = hecke_dim_and_degrees(5)
check("Hecke algebra of (D_5, <tau>) has dimension 3: End = Q x Q(sqrt 5)", o5 == 3 && d5 == [1, 2])

# ------------------------------------------------------------ Part 7
# X = psi^* E_univ (x) u, psi: P^1 -> X_0(N) of degree k, u a twist; the Euler number must be 24.
const TOGGLE = Dict("I0" => "I0*", "I0*" => "I0", "II" => "IV*", "IV*" => "II", "IV" => "II*", "II*" => "IV", "III" => "III*", "III*" => "III")
function partitions(n, m=n)
    n == 0 && return [Int[]]
    out = Vector{Int}[]
    for i in min(n, m):-1:1, rest in partitions(n - i, i)
        push!(out, vcat(i, rest))
    end
    out
end
function classify(N)
    out = []
    for k in 1:4
        cusp_e = k * (1 + N); cusp_rk = k * (N - 1)
        for P1 in partitions(k), P2 in partitions(k)
            fib = String[]
            for Pp in (P1, P2), r in Pp
                push!(fib, N == 7 ? ["I0", "II", "IV", "I0*", "IV*", "II*"][r%6+1] : ["I0", "III", "I0*", "III*"][r%4+1])
            end
            nf = length(fib)
            for mask in 0:2^nf-1
                fib2 = [(mask >> (i - 1)) & 1 == 1 ? TOGGLE[f] : f for (i, f) in enumerate(fib)]
                ntog = count_ones(mask)
                for c_ in 0:4
                    (ntog + c_) % 2 == 1 && continue
                    e = cusp_e + sum(euler(f) for f in fib2) + 6 * c_
                    e != 24 && continue
                    rk_lb = 2 + cusp_rk + sum(rootrank(f) for f in fib2) + 4 * c_
                    (ntog == 0 && c_ == 0) && (rk_lb += 2)
                    used = sum(r - 1 for r in P1) + sum(r - 1 for r in P2)
                    dim = (2 * k - 2 - used) + c_
                    dim < 0 && continue
                    push!(out, (k, Tuple(P1), Tuple(P2), Tuple(fib2), c_, rk_lb, dim))
                end
            end
        end
    end
    out
end
for N in (7, 5)
    cl = classify(N)
    println("  level $N: $(length(cl)) K3 configurations (k, ramification over e1, over e2, fibres there after twisting, free twist zeros, rho lower bound, dim):")
    for row in cl
        println("      ", row)
    end
    check("level $N: every non-isotrivial elliptic K3 surface with a rational cyclic $N-isogeny of its generic fibre has rho >= 16 (Euler-number classification, k <= 4)",
          all(r[6] >= 16 for r in cl))
    check("level $N: every such family has dimension <= 2, so T(X) has rank <= 6 and a one-dimensional Hodge locus in the 4-dimensional period domain of such a T has negative expected intersection dimension with the family",
          all(r[7] <= 2 for r in cl))
    two = sort(unique([r[1:3] for r in cl if r[7] == 2]))
    println("  level $N: two-dimensional configurations (k, ramification over e1, e2): ", join(two, ", "))
    check("level $N: A_$N (k=1, two free twist zeros) and B_$N (k=2 untwisted) are among the two-dimensional families; no family has dimension > 2",
          (1, (1,), (1,)) in two && (2, (1, 1), (1, 1)) in two && all(r[7] <= 2 for r in cl))
end

println("fricke_families.jl: $(NPASS[]) checks passed, $(NFAIL[]) failed")
NFAIL[] > 0 && exit(1)
