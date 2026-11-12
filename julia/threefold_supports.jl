# Exact checks for the support results at the CM point A_0 = E_0^6 (Section VI.H): the vectors of T D_h
# and their images in H^1 of the threefolds, the four points where two threefolds of one family meet,
# the threefolds through a general curve, the weights of the classes [Z_x], the Fourier inversion on the
# four orbits, the weight spaces of H^4 and H^6, and the line of four threefolds of Lemma VI.32 with the
# relations mu_a = m a^2 and the vanishing of sum_x sigma(x)^2 [Z_x] (Theorem VI.33).
# Julia port of code/threefold_supports.py (sixteen checks).
#
# Conventions.  E_0 = C/Z[i]; on the j-th factor B_j = E_0^2 with coordinates (u, v) = (z_j, z_{3+j}) the
# curve C_zeta is u + zeta v = 0; Z_x = C_{x_1} x C_{x_2} x C_{x_3}.  A vector of T D_h is
# v = sum v_{lb} dzbar_b (x) d/dz_l with v_{3+m,b} = Y_{mb}, v_{b,3+m} = (h_{3+m}/h_b) Y_{mb} for
# m, b <= 3 and all other entries zero, Y any 3 x 3 matrix.
#
#   julia --startup-file=no threefold_supports.jl
#
# Exact arithmetic throughout: Gaussian rationals as pairs of Rational{BigInt}; Laurent polynomials in
# h_1..h_6 for the symbolic h (check 10); polynomials in a_j, b_j, c_j, cbar_j (checks 6, 7, 16); elements
# x + y sqrt(d) of Q(i)(sqrt d) for the general points (check 14); rational row reduction (checks 12, 15).
# The random rational data of checks 1, 2, 7 come from a fixed linear congruential generator.  No packages.

module ThreefoldSupports

const R = Rational{BigInt}

# ---------------------------------------------------------------- Gaussian rationals
struct Gq
    re::R
    im::R
end
Gq(x::Integer) = Gq(R(x), R(0))
Gq(x::Rational) = Gq(R(x), R(0))
Base.:+(a::Gq, b::Gq) = Gq(a.re + b.re, a.im + b.im)
Base.:-(a::Gq, b::Gq) = Gq(a.re - b.re, a.im - b.im)
Base.:-(a::Gq) = Gq(-a.re, -a.im)
Base.:*(a::Gq, b::Gq) = Gq(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)
Base.conj(a::Gq) = Gq(a.re, -a.im)
Base.:/(a::Gq, b::Gq) = (a * conj(b)) * Gq(1 // (b.re^2 + b.im^2))
Base.:(==)(a::Gq, b::Gq) = a.re == b.re && a.im == b.im
Base.hash(a::Gq, h::UInt) = hash(a.im, hash(a.re, h))
Base.iszero(a::Gq) = a.re == 0 && a.im == 0
Base.zero(::Type{Gq}) = Gq(0)
const G0 = Gq(0); const G1 = Gq(1); const GI = Gq(R(0), R(1))
const MU4 = [G1, GI, Gq(-1), -GI]
abs2q(a::Gq) = a.re^2 + a.im^2
isgaussint(a::Gq) = denominator(a.re) == 1 && denominator(a.im) == 1
const TRIPLES = [(x1, x2, x3) for x1 in MU4 for x2 in MU4 for x3 in MU4]      # the order of itertools.product
sigma(x) = x[1] * x[2] * x[3]
sq(a::Gq) = a * a

# ---------------------------------------------------------------- a fixed generator of pseudo-random integers
mutable struct LCG
    state::UInt64
end
function next!(g::LCG)
    g.state = g.state * 6364136223846793005 + 1442695040888963407      # arithmetic mod 2^64
    return g.state >> 33
end
randint(g::LCG, lo::Int, hi::Int) = lo + Int(next!(g) % UInt64(hi - lo + 1))

# ---------------------------------------------------------------- Laurent polynomials in h_1..h_6
struct Laurent
    d::Dict{NTuple{6,Int},Gq}
end
lclean(d) = Laurent(filter!(p -> !iszero(p.second), d))
Laurent(c::Gq) = lclean(Dict(ntuple(_ -> 0, 6) => c))
Base.zero(::Type{Laurent}) = Laurent(Dict{NTuple{6,Int},Gq}())
Base.iszero(a::Laurent) = isempty(a.d)
Base.:(==)(a::Laurent, b::Laurent) = a.d == b.d
function Base.:+(a::Laurent, b::Laurent)
    d = copy(a.d)
    for (k, v) in b.d
        d[k] = get(d, k, G0) + v
    end
    return lclean(d)
end
function Base.:*(a::Laurent, b::Laurent)
    d = Dict{NTuple{6,Int},Gq}()
    for (k1, v1) in a.d, (k2, v2) in b.d
        k = k1 .+ k2
        d[k] = get(d, k, G0) + v1 * v2
    end
    return lclean(d)
end
Base.:*(c::Gq, a::Laurent) = Laurent(c) * a
"h_p / h_q"
hratio(p::Int, q::Int) = Laurent(Dict(ntuple(i -> (i == p) - (i == q), 6) => G1))

# ---------------------------------------------------------------- the vectors of T D_h
"the 6 x 6 matrix v[l, b] of the vector of T D_h with matrix Y; ratio(p, q) = h_p / h_q"
function tdh_vector(Y::Matrix{T}, ratio) where {T}
    v = fill(zero(T), 6, 6)
    for m in 1:3, b in 1:3
        v[3+m, b] = Y[m, b]
        v[b, 3+m] = ratio(3 + m, b) * Y[m, b]
    end
    return v
end

"coefficient of dzbar_j in dn_k(v) restricted to the curve C_{sign zeta_j} x {y}: dn_k = dz_k + zeta_k dz_{3+k},
and on C_{s zeta_j} one has dzbar_{3+j} = -s zeta_j dzbar_j"
function kappa_component(v, zeta, k, j, sign)
    frm = [v[k, b] + zeta[k] * v[3+k, b] for b in 1:6]         # coefficients of dzbar_b
    return frm[j] - Gq(sign) * zeta[j] * frm[3+j]
end

# ---------------------------------------------------------------- polynomials in a_1..3, b_1..3, c_1..3, cb_1..3
const Mono = NTuple{12,Int}
const Poly = Dict{Mono,Gq}
pclean(p::Poly) = filter!(q -> !iszero(q.second), p)
var(i::Int) = Poly(ntuple(t -> Int(t == i), 12) => G1)
const AV = [var(j) for j in 1:3]; const BV = [var(3 + j) for j in 1:3]
const CV = [var(6 + j) for j in 1:3]; const CBV = [var(9 + j) for j in 1:3]
function padd(p::Poly, q::Poly, c::Gq=G1)
    r = copy(p)
    for (m, v) in q
        r[m] = get(r, m, G0) + c * v
    end
    return pclean(r)
end
function pmul(p::Poly, q::Poly)
    r = Poly()
    for (m1, v1) in p, (m2, v2) in q
        m = m1 .+ m2
        r[m] = get(r, m, G0) + v1 * v2
    end
    return pclean(r)
end
pscale(c::Gq, p::Poly) = pclean(Poly(m => c * v for (m, v) in p))
factor(j::Int, x::Gq) = padd(padd(padd(AV[j], BV[j]), CV[j], conj(x)), CBV[j], x)
"the class of Z_x: prod_j (a_j + b_j + conj(x_j) c_j + x_j cb_j)"
cls(x) = pmul(pmul(factor(1, x[1]), factor(2, x[2])), factor(3, x[3]))
"coefficient of X_eps = prod (c_j if eps_j = 1, cb_j otherwise)"
function coeff_X(p::Poly, eps)
    m = zeros(Int, 12)
    for j in 1:3
        m[(eps[j] == 1 ? 6 : 9)+j] = 1
    end
    return get(p, Tuple(m), G0)
end
const EPS = [(e1, e2, e3) for e1 in (1, -1) for e2 in (1, -1) for e3 in (1, -1)]

# ---------------------------------------------------------------- monomials of the exterior algebra of A_0
# generators 0..5: dz_1..dz_6; 6..11: dzbar_1..dzbar_6
function weight(g::Int)
    m = g % 6
    s = g < 6 ? 1 : -1             # dz has +, dzbar has -
    e = [0, 0, 0]
    if m < 3
        e[m+1] = s
    else
        e[m-2] = -s                # dz_{3+j} weight -e_j, dzbar_{3+j} weight +e_j
    end
    return e
end
weight_of(mono) = Tuple(sum(weight(g) for g in mono))
"product of two monomials given as sorted lists; returns (sign, monomial) or nothing"
function wedge_mono(m1, m2)
    isempty(intersect(m1, m2)) || return nothing
    seq = vcat(collect(m1), collect(m2))
    sign = 1
    for i in eachindex(seq), j in i+1:length(seq)
        seq[i] > seq[j] && (sign = -sign)
    end
    return sign, sort(seq)
end
function X_mono(eps)
    gens = Int[]
    for j in 0:2
        append!(gens, eps[j+1] == 1 ? [j, 6 + 3 + j] : [6 + j, 3 + j])     # c_j ~ dz_j dzbar_{3+j}, cbar_j ~ dzbar_j dz_{3+j}
    end
    return sort(gens)
end
function subsets(n::Int, r::Int)           # r-subsets of 0..n-1 in lexicographic order
    out = Vector{Int}[]
    function rec(start, cur)
        if length(cur) == r
            push!(out, copy(cur)); return
        end
        for i in start:n-1
            push!(cur, i); rec(i + 1, cur); pop!(cur)
        end
    end
    rec(0, Int[])
    return out
end

# ---------------------------------------------------------------- forms on B_j with coefficients in a ring
# generators 0: dz_j, 1: dz_{3+j}, 2: dzbar_j, 3: dzbar_{3+j}; a form is a dictionary sorted monomial -> coefficient
function wmul(f::Dict{Vector{Int},Gq}, g::Dict{Vector{Int},Gq})
    out = Dict{Vector{Int},Gq}()
    for (m1, c1) in f, (m2, c2) in g
        r = wedge_mono(m1, m2)
        r === nothing && continue
        sgn, m = r
        out[m] = get(out, m, G0) + Gq(sgn) * c1 * c2
    end
    return filter!(p -> !iszero(p.second), out)
end
function curve_class(aa::Gq)
    one = Dict([0] => G1, [1] => aa)                    # dn_a = dz_j + a dz_{3+j}
    two = Dict([2] => G1, [3] => conj(aa))              # dnbar_a
    return Dict(m => GI * Gq(1 // 2) * c for (m, c) in wmul(one, two))
end

# ---------------------------------------------------------------- rational linear algebra
"a basis of the null space of a rational matrix, by row reduction"
function nullspace(M::Matrix{R})
    A = copy(M)
    nr, nc = size(A)
    pivots = Int[]
    r = 0
    for c in 1:nc
        p = findfirst(i -> A[i, c] != 0, r+1:nr)
        p === nothing && continue
        p += r; r += 1
        A[r, :], A[p, :] = A[p, :], A[r, :]
        A[r, :] ./= A[r, c]
        for i in 1:nr
            if i != r && A[i, c] != 0
                A[i, :] .-= A[i, c] .* A[r, :]
            end
        end
        push!(pivots, c)
        r == nr && break
    end
    basis = Vector{R}[]
    for f in setdiff(1:nc, pivots)
        v = zeros(R, nc)
        v[f] = 1
        for (i, c) in enumerate(pivots)
            v[c] = -A[i, f]
        end
        push!(basis, v)
    end
    return basis
end

# ---------------------------------------------------------------- the fields Q(i)(sqrt d), d = 2, 3
struct Sq{D}                    # x + y sqrt(D), x, y in Q(i)
    x::Gq
    y::Gq
end
Base.:+(a::Sq{D}, b::Sq{D}) where {D} = Sq{D}(a.x + b.x, a.y + b.y)
Base.:*(c::Gq, a::Sq{D}) where {D} = Sq{D}(c * a.x, c * a.y)
"x + y sqrt(D) lies in Z[i]: the real and imaginary parts are rational only when y = 0, sqrt(D) being irrational"
in_lattice(a::Sq) = iszero(a.y) && isgaussint(a.x)
in_lattice(a::Gq) = isgaussint(a)

function main()
    npass = 0; nfail = 0
    function check(name, ok)
        println(ok ? "PASS " : "FAIL ", name)
        ok ? (npass += 1) : (nfail += 1)
    end
    rng = LCG(7)

    # ---------------- checks 1, 2: the classes kappa_T(v)_k on the curves
    h = [Gq(R(randint(rng, 1, 9), randint(rng, 1, 9))) for _ in 1:6]
    hr(p, q) = h[p] / h[q]
    ok1 = true; ok2 = true
    for zeta in TRIPLES, j in 1:3, k in 1:3
        k == j && continue
        Y = [Gq(randint(rng, -3, 3)) for _ in 1:3, _ in 1:3]
        v = tdh_vector(Y, hr)
        ok1 &= kappa_component(v, zeta, k, j, 1) == zeta[k] * Y[k, j] - zeta[j] * hr(3 + j, k) * Y[j, k]
        ok2 &= kappa_component(v, zeta, k, j, -1) == zeta[k] * Y[k, j] + zeta[j] * hr(3 + j, k) * Y[j, k]
        E = [Gq((a, b) == (j, k) ? 1 : 0) for a in 1:3, b in 1:3]
        vE = tdh_vector(E, hr)
        ok1 &= iszero(kappa_component(vE, zeta, k, j, 1) + zeta[j] * hr(3 + j, k))
        ok2 &= iszero(kappa_component(vE, zeta, k, j, -1) - zeta[j] * hr(3 + j, k))
        ok2 &= !iszero(kappa_component(vE, zeta, k, j, -1))
    end
    check("kappa_T(v)_k on Gamma_y is (zeta_k Y_kj - zeta_j h_{3+j}/h_k Y_jk) dzbar_j, equal to -zeta_j h_{3+j}/h_k at Y = E_jk, for all 64 zeta and j != k", ok1)
    check("kappa_T'(v)_k on Gamma'_y is (zeta_k Y_kj + zeta_j h_{3+j}/h_k Y_jk) dzbar_j, nonzero at Y = E_jk", ok2)

    # ---------------- check 3: C_u and C_{-u} meet in the four points of order two
    HALF = [Gq(R(a, 2), R(b, 2)) for a in 0:1 for b in 0:1]              # (1/2)Z[i] / Z[i]
    ok3 = true
    for u in MU4
        pts = [(a, b) for a in HALF for b in HALF if in_lattice(a + u * b)]
        ok3 &= length(pts) == 4 && all(in_lattice(a - u * b) for (a, b) in pts)
        ok3 &= Set(a for (a, b) in pts) == Set(HALF)          # every point of C_u with 2x = 0 is one of them
    end
    check("C_u and C_{-u} meet exactly in the four points of order two of C_u (|2u|^2 = 4), for every u", ok3)

    # ---------------- check 4: the coordinates n'_j on C_{zeta_j} and n_j on C_{-zeta_j}
    # linear forms c z in the coordinate z = z_j of the curve, given by their coefficient c
    ok4 = true
    for zeta in MU4
        zc = conj(zeta)
        ok4 &= (G1 - zeta * (-zc)) - Gq(2) == G0             # n' on C_zeta: z_{3+j} = -conj(zeta) z_j
        ok4 &= (G1 + zeta * zc) - Gq(2) == G0                # n on C_{-zeta}: z_{3+j} = conj(zeta) z_j
        ok4 &= G1 + zeta * (-zc) == G0                       # n vanishes on C_zeta
    end
    check("n'_j restricts to 2 z_j on C_{zeta_j} and n_j to 2 z_j on C_{-zeta_j}", ok4)

    # ---------------- check 5: the threefolds through a general Gamma_y
    ok5 = true
    for zeta in TRIPLES, j in 1:3
        k, l = [m for m in 1:3 if m != j]
        meeting = [xi for xi in TRIPLES if xi[k] == zeta[k] && xi[l] == zeta[l]]
        ok5 &= length(meeting) == 4
        fam = Set(xi for xi in meeting if sq(sigma(xi)) == G1)
        if sq(sigma(zeta)) == G1                              # zeta in the family sigma = +-1
            zj = ntuple(m -> m == j ? -zeta[m] : zeta[m], 3)
            ok5 &= fam == Set([zeta, zj]) && length(fam) == 2
        else                                                  # otherwise the two of that family have xi_j = +-i zeta_j
            other = [ntuple(m -> m == j ? s * zeta[m] : zeta[m], 3) for s in (GI, -GI)]
            ok5 &= fam == Set(other) && length(fam) == 2
        end
    end
    check("the threefolds meeting a general Gamma_y are the four with xi_k = zeta_k, xi_l = zeta_l; among the thirty-two of the family of zeta only Z_zeta and Z_zeta^(j), and for zeta of the other family the two with xi_j = +-i zeta_j", ok5)

    # ---------------- check 6: the coefficient of X_eps in [Z_x]
    ok6 = true
    for x in TRIPLES
        Zx = cls(x)
        for eps in EPS
            want = sigma(x)
            for j in 1:3
                eps[j] == 1 && (want = want * sq(x[j]))
            end
            ok6 &= coeff_X(Zx, eps) == want
        end
    end
    check("coefficient of X_eps in [Z_x] is sigma(x) prod_{eps_j = 1} c(x)_j, all 64 x and 8 eps", ok6)

    # ---------------- check 7: Fourier inversion on the four orbits, and the signed sum of the thirty-two
    ok7 = true
    nu = Dict(x => Gq(R(randint(rng, -5, 5), randint(rng, 1, 3))) for x in TRIPLES)
    total = Poly()
    for x in TRIPLES
        total = padd(total, cls(x), nu[x])
    end
    F = Dict(eps => coeff_X(total, eps) for eps in EPS)
    for cvec in EPS
        W = G0
        for x in TRIPLES
            all(sq(x[j]) == Gq(cvec[j]) for j in 1:3) && (W += nu[x] * sigma(x))
        end
        inv = G0
        for eps in EPS
            chi = prod(cvec[j] for j in 1:3 if eps[j] == 1; init=1)
            inv += F[eps] * Gq(chi)
        end
        ok7 &= W == Gq(1 // 8) * inv
    end
    signed = Poly()
    for x in TRIPLES
        sq(sigma(x)) == G1 && (signed = padd(signed, cls(x), sigma(x)))
    end
    Fs = Dict(eps => coeff_X(signed, eps) for eps in EPS)
    ok7 &= Fs[(1, 1, 1)] == Gq(32) && Fs[(-1, -1, -1)] == Gq(32) &&
           all(iszero(Fs[e]) for e in EPS if e != (1, 1, 1) && e != (-1, -1, -1))
    check("W_c = (1/8) sum_eps F(eps) chi_eps(c) for random nu; the signed sum of the thirty-two has X-coefficients 32 at +-(1,1,1) and 0 elsewhere (N p = 32, W_c = 8)", ok7)

    # ---------------- checks 8, 9: the exterior algebra of A_0, theta_h X_eps = 0 and the weights
    ok8 = true
    for eps in EPS
        X = X_mono(eps)
        for m in 0:5                                           # theta_h = sum h_m dz_m dzbar_m
            ok8 &= wedge_mono([m, 6 + m], X) === nothing
        end
        ok8 &= weight_of(X) == Tuple(2 .* eps)
    end
    check("theta_h X_eps = 0 term by term, and X_eps has weight 2 eps", ok8)

    ok9 = true
    w4 = Set(weight_of(mono) for mono in subsets(12, 4))
    ok9 &= all(!(Tuple(2 .* eps) in w4) && !(Tuple(-2 .* eps) in w4) for eps in EPS)
    for eps in EPS
        monos = [mono for mono in subsets(12, 6) if weight_of(mono) == Tuple(2 .* eps)]
        ok9 &= monos == [X_mono(eps)]
    end
    check("H^4(A_0) has no class of weight +-2 eps, and X_eps spans the weight 2 eps part of H^6(A_0)", ok9)

    # ---------------- checks 10-16: the line of four threefolds (Lemma VI.32) and the sixty-four (Theorem VI.33)
    # check 10: at Y = E_jk the vector v gives dn_a(v) = a dzbar_k, dn_k(v) = (h_{3+j}/h_k) dzbar_{3+j}, dn_l(v) = 0,
    # with h_1, ..., h_6 indeterminates
    ok10 = true
    for j in 1:3, k in 1:3
        k == j && continue
        l = 6 - j - k
        Y = [Laurent((a, b) == (j, k) ? G1 : G0) for a in 1:3, b in 1:3]
        v = tdh_vector(Y, hratio)
        for xi_k in MU4, xi_l in MU4, aa in MU4
            dn_a = [v[j, bb] + aa * v[3+j, bb] for bb in 1:6]               # coefficients of dzbar_b in dn_a(v)
            dn_k = [v[k, bb] + xi_k * v[3+k, bb] for bb in 1:6]
            dn_l = [v[l, bb] + xi_l * v[3+l, bb] for bb in 1:6]
            ok10 &= all(dn_a[bb] == Laurent(bb == k ? aa : G0) for bb in 1:6)
            ok10 &= all(dn_k[bb] == (bb == 3 + j ? hratio(3 + j, k) : zero(Laurent)) for bb in 1:6)
            ok10 &= all(iszero(dn_l[bb]) for bb in 1:6)
        end
    end
    check("at Y = E_jk: dn_a(v) = a dzbar_k, dn_k(v) = (h_{3+j}/h_k) dzbar_{3+j}, dn_l(v) = 0, for all j != k, a, xi_k, xi_l", ok10)

    # check 11: [C_a] wedge dzbar_{3+j} = (i/2)(dz_j + a dz_{3+j}) dzbar_j dzbar_{3+j}, and the two relations;
    # a linear form in mu_1, mu_i, mu_-1, mu_-i is the vector of its four coefficients
    half_i = GI * Gq(1 // 2)
    dzbar3j = Dict([3] => G1)
    ok11 = true
    total11 = Dict([0, 2, 3] => fill(G0, 4), [1, 2, 3] => fill(G0, 4))
    for (n, aa) in enumerate(MU4)
        w = wmul(curve_class(aa), dzbar3j)
        ok11 &= w == Dict([0, 2, 3] => half_i, [1, 2, 3] => half_i * aa)
        for (mono, cf) in w
            haskey(total11, mono) ? (total11[mono][n] += cf) : (ok11 = false)
        end
    end
    rel1 = [c * Gq(2) / GI for c in total11[[0, 2, 3]]]
    rel2 = [c * Gq(2) / GI for c in total11[[1, 2, 3]]]
    ok11 &= rel1 == fill(G1, 4) && rel2 == MU4
    check("[C_a] dzbar_{3+j} = (i/2)(dz_j + a dz_{3+j}) dzbar_j dzbar_{3+j}; the coefficients of sum mu_a [C_a] dzbar_{3+j} are sum mu_a and sum a mu_a", ok11)

    # check 12: the rational solutions of the two relations are mu_a = m a^2
    M12 = Matrix{R}(undef, 3, 4)
    for n in 1:4
        M12[1, n] = rel1[n].re; M12[2, n] = rel2[n].re; M12[3, n] = rel2[n].im
    end
    ns12 = nullspace(M12)
    ok12 = all(c -> c.im == 0, rel1) && length(ns12) == 1 && ns12[1][1] != 0
    ok12 = ok12 && [Gq(ns12[1][n] / ns12[1][1]) for n in 1:4] == [sq(aa) for aa in MU4]
    check("the relations sum mu_a = 0, sum a mu_a = 0 have the one-dimensional solution space mu_a = m a^2, i.e. mu_1 = mu_-1 = -mu_i = -mu_-i", ok12)

    # check 13: Q . C_b = 8, Q^2 = 32, and C_1 meets C_i in |1 - i|^2 = 2 points: Q has finite stabiliser
    QUARTER = [Gq(R(p, 4), R(q, 4)) for p in 0:3 for q in 0:3]            # (1/4)Z[i] / Z[i]
    ok13 = true
    for bb in MU4
        ok13 &= sum(abs2q(aa - bb) for aa in MU4 if aa != bb) == 8
    end
    ok13 &= sum(abs2q(aa - bb) for aa in MU4 for bb in MU4 if aa != bb) == 32
    for aa in MU4, bb in MU4
        if aa != bb
            pts = [u for u in QUARTER if in_lattice((aa - bb) * u)]       # u = z_j on C_a cap C_b, with z_{3+j} = -conj(a) u
            ok13 &= length(pts) == abs2q(aa - bb)
        end
    end
    ok13 &= length([u for u in QUARTER if in_lattice((G1 - GI) * u)]) == 2
    check("Q . C_b = 8 for every b, Q^2 = 32, and C_a meets C_b in |a - b|^2 points, 2 for (1, i): Q is ample with finite stabiliser", ok13)

    # check 14: the threefolds meeting Q x {y} for general y in Pi = C_{xi_k} x C_{xi_l} are the four T_a;
    # the general point has coordinates sqrt(2)/7 on C_{xi_k} and sqrt(3)/11 on C_{xi_l}
    tk = Sq{2}(G0, Gq(1 // 7)); tl = Sq{3}(G0, Gq(1 // 11))
    ok14 = true
    for j in 1:3, k in 1:3
        k == j && continue
        l = 6 - j - k
        for xi_k in MU4, xi_l in MU4
            yk = (tk, (-conj(xi_k)) * tk)                      # a point of C_{xi_k} off the other curves
            yl = (tl, (-conj(xi_l)) * tl)
            meeting = [x for x in TRIPLES if in_lattice(yk[1] + x[k] * yk[2]) && in_lattice(yl[1] + x[l] * yl[2])]
            ok14 &= Set(meeting) == Set(x for x in TRIPLES if x[k] == xi_k && x[l] == xi_l)
            ok14 &= length(meeting) == 4 && length(Set(sigma(x) for x in meeting if sq(sigma(x)) == G1)) == 2
        end
    end
    check("the threefolds meeting Q x {y}, y general in Pi, are the four T_a, two of each family, for all j, k, xi_k, xi_l", ok14)

    # check 15: mu_x / x_j^2 independent of x_j for each j forces mu_x = m sigma(x)^2
    index = Dict(x => n for (n, x) in enumerate(TRIPLES))
    rows = Vector{R}[]
    for x in TRIPLES, j in 1:3, aa in MU4
        aa == x[j] && continue
        xp = ntuple(jj -> jj == j ? aa : x[jj], 3)
        row = zeros(R, 64)
        row[index[x]] += sq(x[j]).re                           # x_j^{-2} = x_j^2 = +-1
        row[index[xp]] -= sq(xp[j]).re
        push!(rows, row)
    end
    M15 = Matrix{R}(undef, length(rows), 64)
    for (i, row) in enumerate(rows)
        M15[i, :] = row
    end
    ns = nullspace(M15)
    ok15 = length(ns) == 1 && length(rows) == 576
    if ok15
        ref = ns[1][index[(G1, G1, G1)]]
        ok15 &= ref != 0 && all(Gq(ns[1][n] / ref) == sq(sigma(x)) for (n, x) in enumerate(TRIPLES))
    end
    check("the relations along all lines of four threefolds have the one-dimensional solution space mu_x = m sigma(x)^2", ok15)

    # check 16: sum_x sigma(x)^2 [Z_x] = prod_j T_{2,j} = 0 in H^6(A_0), T_{2,j} = sum_a a^2 [C_a] = 0 in H^2(B_j)
    s16 = Poly()
    for x in TRIPLES
        s16 = padd(s16, cls(x), sq(sigma(x)))
    end
    ok16 = isempty(s16)
    for j in 1:3
        t = Poly()
        for aa in MU4
            t = padd(t, factor(j, aa), sq(aa))
        end
        ok16 &= isempty(t)
    end
    d16 = Poly()
    for x in TRIPLES
        s2 = sq(sigma(x))
        s2 == G1 && (d16 = padd(d16, cls(x)))
        s2 == Gq(-1) && (d16 = padd(d16, cls(x), Gq(-1)))
    end
    ok16 &= isempty(d16)
    check("sum_x sigma(x)^2 [Z_x] = 0: T_{2,j} = 0 for each j, and the sum over the family sigma = +-1 equals the sum over sigma = +-i", ok16)

    println("threefold_supports.jl: $npass checks passed, $nfail failed")
    return nfail
end

end # module

if abspath(PROGRAM_FILE) == @__FILE__
    exit(ThreefoldSupports.main() > 0 ? 1 : 0)
end
