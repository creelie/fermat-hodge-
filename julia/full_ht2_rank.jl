# full_ht2_rank.jl -- the Hochschild rank on Y = S_1 x S_2 for the RM class (Proposition prop:kplus).
# H~(S) = C^24 (index 1 = H^0, 2..23 = H^2, 24 = H^4), Mukai pairing <1,pt> = -1, q on H^2.
# HT^2(S) = H^0(wedge^2 T) + H^1(T) + H^2(O) acts by the Mukai-skew operators
#   xi_a(x) = [a <sbar, x> - sbar <a, x>] / <sbar, s>,  a in s^perp cap sbar^perp = C.1 + H^{1,1} + C.pt
# (a = 1: contraction with the bivector; a in H^{1,1}: kappa; a = pt: cup with t in H^{0,2}),
# checked against the literal operators.  For the Mukai vector v in H~(S_1) (x) H~(S_2)
# (a 24 x 24 matrix V), with phi~ = V^T Q~ : H~(S_1) -> H~(S_2) and M its U + N block:
#   R(v) = rank{(xi_1 (x) 1 + 1 (x) xi_2) v : xi_i in HT^2(S_i)}  =  46 - 2m - dim E,
#   r(v) = the same rank without the bivectors                     =  44 - 2m - dim E_r,
#   rc   = the rank on H^1(T) only                                 =  40 - (2m - 2 + dim E_c),
# E = ker(M^* M - c^2 e) on (U+N)_C, E_r = E cap pt^perp cap (M^* pt)^perp, E_c = E_r cap 1^perp
# cap (M^* 1)^perp, and <v,v> = 2 m e c^2 + tr(M^* M).  Seven shapes of v for e in {2,3,5,7},
# m in {3,4,5,7,10} (140 cases); the control v = identity (O_Delta) gives R = 22, r = 21.
# The rank computed with the untwisted ch in place of v differs from R.
# Floating point (Float64, SVD with relative threshold 1e-8; the spectral gaps are printed).
# Run: julia --startup-file=no full_ht2_rank.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms
using LinearAlgebra, Random

function model(e, m, rng)
    s = sqrt(e); nL = 2m; nN = 22 - nL
    Q = zeros(22, 22); P = zeros(22, 22)
    for i in 0:m-1
        Q[2i+1:2i+2, 2i+1:2i+2] = i < 2 ? [0.0 2e; 2e 0.0] : [-2.0 0.0; 0.0 -2.0e]
        P[2i+1:2i+2, 2i+1:2i+2] = [0.0 e; 1.0 0.0]
    end
    QN = -Matrix(1.0I, nN, nN); QN[1, 1] = 1.0
    Q[nL+1:end, nL+1:end] = QN
    Lp = zeros(22, m); Lm = zeros(22, m)
    for i in 0:m-1
        Lp[2i+1, i+1] = s; Lp[2i+2, i+1] = 1.0; Lm[2i+1, i+1] = -s; Lm[2i+2, i+1] = 1.0
    end
    base = Lp[:, 1:2]; Wv = base
    while true
        Wv = base + 0.3 * (hcat(Lp, Lm) * randn(rng, 2m, 2))
        all(eigvals(Symmetric(Wv' * Q * Wv)) .> 1e-3) && break
    end
    e1 = Wv[:, 1] / sqrt(Wv[:, 1]' * Q * Wv[:, 1]); v2 = Wv[:, 2] - (e1' * Q * Wv[:, 2]) * e1
    w1 = e1 + im * v2 / sqrt(v2' * Q * v2)
    return Q, P, w1, nL, nN
end
function mukai(Q)
    Qt = zeros(24, 24); Qt[2:23, 2:23] = Q; Qt[1, 24] = Qt[24, 1] = -1.0
    return Qt
end
bil(x, A, y) = transpose(x) * A * y            # bilinear (no conjugation), as in numpy x @ A @ y
nullbasis(M, k) = (F = svd(M; full = true); F.V[:, k+1:end])
function tangent_basis(Qt, s)
    one = zeros(ComplexF64, 24); one[1] = 1; pt = zeros(ComplexF64, 24); pt[24] = 1
    Mh = vcat(transpose(Qt[2:23, 2:23] * s[2:23]), transpose(Qt[2:23, 2:23] * conj(s[2:23])))
    H11 = zeros(ComplexF64, 24, 20); H11[2:23, :] = nullbasis(Mh, 2)
    return vcat([one, pt], [H11[:, j] for j in 1:20])
end
function xi(Qt, s, a)
    sb = conj(s); q = bil(sb, Qt, s)
    return (a * transpose(Qt * sb) - sb * transpose(Qt * a)) / q     # Qt symmetric
end
function literal_ops(Q, w)
    wb = conj(w); q = bil(wb, Q, w)
    T = zeros(ComplexF64, 24, 24); T[2:23, 1] = wb; T[24, 2:23] = Q * wb
    Pi = zeros(ComplexF64, 24, 24); Pi[1, 2:23] = (Q * wb) / q; Pi[2:23, 24] = wb / q
    return T, Pi
end
function numrank(A)
    sv = svdvals(A); sv = sv / sv[1]
    return count(>(1e-8), sv), sv
end
function ranks(Qt, s1, s2, V, Vg)
    X1 = [xi(Qt, s1, a) for a in tangent_basis(Qt, s1)]; X2 = [xi(Qt, s2, a) for a in tangent_basis(Qt, s2)]
    function rk(Vm, drop)
        cols = Vector{ComplexF64}[]
        for (k, X) in enumerate(X1); (drop && k == 1) || push!(cols, vec(X * Vm)); end
        for (k, X) in enumerate(X2); (drop && k == 1) || push!(cols, vec(Vm * transpose(X))); end
        return numrank(hcat(cols...))
    end
    R, svR = rk(V, false); r, _ = rk(V, true)
    rc, _ = numrank(hcat(vcat([vec(X * V) for X in X1[3:end]], [vec(V * transpose(X)) for X in X2[3:end]])...))
    k = R; gap = (svR[k], k < length(svR) ? svR[k+1] : 0.0)
    Ru = Vg === nothing ? nothing : rk(Vg, false)[1]
    return R, r, rc, Ru, gap
end
function predictions(Qt, V, nL, c, e)
    phit = transpose(V) * Qt
    adj = Qt \ (transpose(phit) * Qt)
    MM = adj * phit
    idx = vcat([1], collect(nL+2:23), [24]); Lidx = collect(2:nL+1)
    MMu = MM[idx, idx]
    cross = max(maximum(abs.(phit[Lidx, idx])), maximum(abs.(phit[idx, Lidx])))
    K = MMu - c^2 * e * I
    sv = svdvals(K); dimE = count(<(1e-8 * max(1.0, sv[1])), sv)
    Ef = zeros(ComplexF64, 24, dimE)
    dimE > 0 && (Ef[idx, :] = nullbasis(K, length(idx) - dimE))
    pt = zeros(24); pt[24] = 1; one = zeros(24); one[1] = 1
    Mpt = adj * pt; Mone = adj * one
    rkC(rows) = dimE == 0 ? 0 : rank(vcat([transpose(Qt * r) for r in rows]...) * Ef; atol = 1e-8)
    dimEr = dimE - rkC([pt, Mpt]); dimEc = dimE - rkC([pt, one, Mpt, Mone])
    return dimE, dimEr, tr(MM), tr(MMu), cross, dimEc
end
function hodge_defect(Qt, s1, s2, V)
    phit = transpose(V) * Qt; img = phit * s1
    d1 = norm(img - (bil(conj(s2), Qt, img) / bil(conj(s2), Qt, s2)) * s2)
    d2 = maximum(abs(bil(s2, Qt, phit * a)) for a in tangent_basis(Qt, s1))
    return max(d1, d2)
end
function sqrt_td(); Mt = Matrix(1.0I, 24, 24); Mt[24, 1] = 1.0; Mt; end
function gamma_to_V(Q, P, nL, nN, c, sh, rng)
    G = zeros(24, 24)
    G[2:23, 2:23] += c * (Q \ transpose(P))
    G[1, 1] += get(sh, :r, 0); G[24, 1] += get(sh, :a, 0); G[1, 24] += get(sh, :b, 0); G[24, 24] += get(sh, :d, 0)
    if get(sh, :generic, false)
        nvec() = (v = zeros(22); v[nL+1:end] = rand(rng, -3:3, nN); v)
        G[2:23, 1] += nvec(); G[1, 2:23] += nvec(); G[24, 2:23] += nvec(); G[2:23, 24] += nvec()
        Xi = zeros(22, 22); Xi[nL+1:end, nL+1:end] = rand(rng, -3:3, nN, nN); G[2:23, 2:23] += Xi
    end
    T = sqrt_td()
    return T * G * transpose(T), G
end
function similitude_V(Q, P, nL, nN, c, e, rng)
    Qt = mukai(Q); idx = vcat([1], collect(nL+2:23), [24])
    G = Qt[idx, idx]; A = randn(rng, length(idx), length(idx)); A = A - transpose(A)
    O = exp((G \ A) * 0.3)
    @assert maximum(abs.(transpose(O) * G * O - G)) < 1e-9
    phit = zeros(24, 24); phit[2:nL+1, 2:nL+1] = c * P[1:nL, 1:nL]; phit[idx, idx] = c * sqrt(e) * O
    return Qt \ transpose(phit)
end

function main()
    C = Checks("full_ht2_rank.jl")
    for (e, m) in [(2, 4), (5, 10)]
        Q, P, w1, nL, nN = model(e, m, MersenneTwister(1)); Qt = mukai(Q)
        s = zeros(ComplexF64, 24); s[2:23] = w1
        T, Pi = literal_ops(Q, w1); q = bil(conj(w1), Q, w1)
        pt = zeros(ComplexF64, 24); pt[24] = 1; one = zeros(ComplexF64, 24); one[1] = 1
        dev = max(maximum(abs.(xi(Qt, s, q * pt) - T)), maximum(abs.(xi(Qt, s, one) - Pi)))
        check(C, "e=$e m=$m: xi_1 = bivector contraction and xi_{q pt} = cup with wbar (max deviation $(round(dev, sigdigits=2)))", dev < 1e-12)
    end
    shapes = [Dict(:r => 0, :a => 1, :b => 2), :abec, Dict(:r => 3, :a => -1, :b => 5, :d => 2),
              Dict(:r => 2, :a => 1, :b => -1, :d => 1, :generic => true), :sim, :abzero, :jordan1]
    untw_differs = false; mingap = Inf
    for e in (2, 3, 5, 7), m in (3, 4, 5, 7, 10)
        okall = true; Rs = Int[]
        for sh0 in shapes
            rng = MersenneTwister(100e + m)
            Q, P, w1, nL, nN = model(e, m, rng); Qt = mukai(Q)
            s1 = zeros(ComplexF64, 24); s1[2:23] = w1
            if sh0 === :sim
                V = similitude_V(Q, P, nL, nN, 1.0, e, rng); Vg = nothing
            else
                sh = sh0 === :abec ? Dict(:r => 0, :a => 1, :b => e) :
                     sh0 === :abzero ? Dict(:r => 1, :a => -1, :b => -1, :d => e + 1) :
                     sh0 === :jordan1 ? Dict(:r => 1, :a => -1, :b => 1, :d => e - 1) : sh0
                V, Vg = gamma_to_V(Q, P, nL, nN, 1.0, sh, rng)
            end
            phit = transpose(V) * Qt; s2 = phit * s1
            hd = hodge_defect(Qt, s1, s2, V)
            R, r, rc, Ru, gap = ranks(Qt, s1, s2, V, Vg)
            dimE, dimEr, vv, trMM, cross, dimEc = predictions(Qt, V, nL, 1.0, e)
            ok = R == 46 - 2m - dimE && r == 44 - 2m - dimEr && rc == 40 - (2m - 2 + dimEc) &&
                 hd < 1e-8 && cross < 1e-12 && abs(vv - (2m * e + trMM)) < 1e-8
            okall &= ok; push!(Rs, R); mingap = min(mingap, gap[1] / max(gap[2], 1e-300))
            (Ru !== nothing && Ru != R) && (untw_differs = true)
        end
        check(C, "e=$e m=$m, 7 shapes: R = 46-2m-dim E, r = 44-2m-dim E_r, rc = 40-(2m-2+dim E_c), <v,v> = 2me c^2 + tr M*M, v Hodge (R = $Rs)", okall)
    end
    check(C, "the rank with the untwisted chern character in place of the Mukai vector differs from R in some case", untw_differs)
    Q, P, w1, nL, nN = model(2, 5, MersenneTwister(5)); Qt = mukai(Q)
    s1 = zeros(ComplexF64, 24); s1[2:23] = w1
    for (name, Dm) in [("identity", Matrix(1.0I, 24, 24)), ("-dual", Diagonal(vcat([-1.0], ones(22), [-1.0])))]
        V = Qt \ transpose(Matrix(Dm))
        R, r, _, _, _ = ranks(Qt, s1, s1, V, nothing)
        check(C, "control v = $name (O_Delta): R = $R = 22 = dim HH^2(S), r = $r = 21", R == 22 && r == 21)
    end
    finish(C)
end
main()
