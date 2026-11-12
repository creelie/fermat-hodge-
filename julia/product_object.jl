# product_object.jl -- port of code/product_object.py.
# The exterior-algebra model of H^*(A x A') at a product point of the Weil
# family, (m,m') = (2,1) and (2,2): H^1 has basis e_j, f_j (j = 0..2n-1),
# H^{1,0} = <e_j (j<n), f_j (j>=n)>, theta = i sum_j s_j e_j f_j,
# omega_+ = e_0...e_{2n-1}, omega_- = f_0...f_{2n-1}; HT^1 = H^{0,1} (+) T acts
# by wedging f_j (j<n), e_j (j>=n) and contracting e_j (j<n), f_j (j>=n).
# Checks: dim T D_{n,n} = n^2, the product locus, the first-order Hodge loci,
# the vanishing of the cross terms, Hankel rank 3, aH = 9 and 16, r = 57 and 104.
# As in the Python program the ranks are numerical (singular values with
# relative tolerance 1e-7, complex double precision, generic data from a
# fixed seed); every rank is an integer.
# Run: julia --startup-file=no product_object.jl
using LinearAlgebra, Random, Printf

# ---- exterior algebra on 4n generators; monomials are bit masks
# (generator e_j -> bit 2j, f_j -> bit 2j+1), coefficients ComplexF64 ----
const C = ComplexF64
const Elt = Dict{UInt32,C}
const zeta = (-1 + im * sqrt(3)) / 2
bit(g) = UInt32(1) << g
gen(g) = Elt(bit(g) => C(1))
e_(j) = gen(2j); f_(j) = gen(2j + 1)
one_() = Elt(UInt32(0) => C(1))
clean!(r::Elt) = (filter!(p -> abs(p.second) > 1e-12, r); r)
function add(a::Elt, b::Elt, cb=1.0)
    r = copy(a)
    for (k, v) in b
        r[k] = get(r, k, C(0)) + cb * v
    end
    clean!(r)
end
scal(a::Elt, c) = Elt(k => c * v for (k, v) in a)
function wedge(a::Elt, b::Elt)
    r = Elt()
    for (ka, va) in a, (kb, vb) in b
        ka & kb != 0 && continue
        s = 0; t = kb
        while t != 0
            y = trailing_zeros(t); t &= t - UInt32(1)
            s += count_ones(ka >> (y + 1))
        end
        k = ka | kb
        r[k] = get(r, k, C(0)) + (isodd(s) ? -va * vb : va * vb)
    end
    clean!(r)
end
function contract(g::Int, a::Elt)
    r = Elt(); bg = bit(g)
    for (k, v) in a
        k & bg == 0 && continue
        pos = count_ones(k & (bg - UInt32(1)))
        r[k ⊻ bg] = isodd(pos) ? -v : v
    end
    r
end
wedge_gen(g::Int, a::Elt) = wedge(gen(g), a)
function power(a::Elt, k::Int)
    r = one_()
    for _ in 1:k
        r = wedge(r, a)
    end
    r
end
function expo(a::Elt, top::Int)
    r = one_(); term = one_()
    for k in 1:top
        term = scal(wedge(term, a), 1.0 / k)
        r = add(r, term)
    end
    r
end
"dense coordinate vector (index = mask + 1)"
function vec_(n, a::Elt)
    v = zeros(C, 1 << (4n))
    for (k, c) in a
        v[k+1] = c
    end
    v
end

"numerical rank: singular values above tol * (largest singular value)"
function rank_(M::AbstractMatrix, tol=1e-7)
    isempty(M) && return 0
    s = svdvals(Matrix(M))
    s[1] > 0 ? count(>(tol * s[1]), s) : 0
end

# operators: ('w', g) wedges the generator g, ('c', g) contracts with its dual
function ops(n)
    w = vcat([2j + 1 for j in 0:n-1], [2j for j in n:2n-1])   # H^{0,1}
    c = vcat([2j for j in 0:n-1], [2j + 1 for j in n:2n-1])   # T = (H^{1,0})^*
    w, c
end
apply_op(op, a::Elt) = op[1] == 'w' ? wedge_gen(op[2], a) : contract(op[2], a)
ht1_ops(n) = ((w, c) = ops(n); vcat([('w', g) for g in w], [('c', g) for g in c]))
h1T_ops(n) = ((w, c) = ops(n); [(('w', a), ('c', v)) for a in w for v in c])
ht2_ops(n) = (o = ht1_ops(n); [(o[i], o[j]) for i in 1:length(o) for j in i+1:length(o)])
"rows: the classes o(gamma) for o in op_list; the zero columns are dropped"
function cmat(gammas::Vector{Elt}, op_list)
    cols = Dict{UInt64,Int}(); ents = Tuple{Int,Int,C}[]
    for (i, o) in enumerate(op_list), (t, g) in enumerate(gammas)
        a = g
        for op in o
            a = apply_op(op, a)
        end
        for (k, v) in a
            j = get!(cols, (UInt64(t) << 32) | k, length(cols) + 1)
            push!(ents, (i, j, v))
        end
    end
    M = zeros(C, length(op_list), length(cols))
    for (i, j, v) in ents
        M[i, j] = v
    end
    M
end
ann_dim(gammas::Vector{Elt}, op_list) = length(op_list) - rank_(cmat(gammas, op_list))
contraction_rank(gamma::Elt, op_list) = rank_(cmat([gamma], op_list))
function hankel_rank(cs, n)
    mu = [factorial(k) * cs[k+1] for k in 0:2n]
    rank_(C[mu[j+i+1] for j in 0:2n-2, i in 0:2])
end

const NPASS = Ref(0); const NFAIL = Ref(0)
function check(name, ok)
    ok ? (NPASS[] += 1) : (NFAIL[] += 1)
    println(ok ? "PASS " : "FAIL ", name)
end
crandn(rng) = randn(rng) + im * randn(rng)

function run(rng, n, m, expect)
    mp = n - m
    tag = "n=$n (m,m')=($m,$mp)"
    IA = vcat(0:m-1, n:n+m-1); IB = [j for j in 0:2n-1 if !(j in IA)]
    function theta(I)
        t = Elt()
        for j in I
            t = add(t, wedge(e_(j), f_(j)), im * (j < n ? 1 : -1))
        end
        t
    end
    function om(I, plus)
        r = one_()
        for j in I
            r = wedge(r, plus ? e_(j) : f_(j))
        end
        r
    end
    thA, thB = theta(IA), theta(IB); th = add(thA, thB)
    opA, omA = om(IA, true), om(IA, false); opB, omB = om(IB, true), om(IB, false)
    u, up = crandn(rng), crandn(rng)
    # rational Weil classes of the factors: omega_1 = u om_+ + conj(u) om_-, omega_2 = zeta_* omega_1
    weil(opl, oml, uu, lam) = add(scal(opl, lam * uu), scal(oml, conj(lam * uu)))
    wA1, wA2 = weil(opA, omA, u, 1), weil(opA, omA, u, zeta^(2m))
    wB1 = weil(opB, omB, up, 1)
    Wp = wedge(opA, opB); Wm = wedge(omA, omB)
    H1T = h1T_ops(n); HT2 = ht2_ops(n)
    println("=== $tag: product of a Weil $(2m)-fold A and a Weil $(2mp)-fold A' ===")
    check("$tag dim H^1(T) = $(4n*n), dim HT^2 = $(binomial(4n, 2))",
          length(H1T) == 4n * n && length(HT2) == binomial(4n, 2))
    TD = ann_dim([th, Wp, Wm], H1T)
    check("$tag dim T D_(n,n) = $TD = n^2", TD == n * n)
    w_, c_ = ops(n)
    blockA = [(('w', a), ('c', v)) for a in w_ for v in c_ if (a ÷ 2 in IA) && (v ÷ 2 in IA)]
    blockB = [(('w', a), ('c', v)) for a in w_ for v in c_ if (a ÷ 2 in IB) && (v ÷ 2 in IB)]
    TA = ann_dim([thA, opA, omA], blockA); TB = ann_dim([thB, opB, omB], blockB)
    check("$tag dim T(product locus) = $TA + $TB = m^2 + m'^2, mixed directions = $(n*n-TA-TB) = 2mm'",
          TA == m * m && TB == mp * mp && n * n - TA - TB == 2m * mp)
    N, Np = 1.0, 1.0
    cA = randn(rng, 2m + 1); cB = randn(rng, 2mp + 1)
    pA = Elt(); pB = Elt()
    for k in 0:2m
        pA = add(pA, power(thA, k), cA[k+1])
    end
    for k in 0:2mp
        pB = add(pB, power(thB, k), cB[k+1])
    end
    chF = add(scal(wA1, N), pA); chF2 = add(scal(wA2, N), pA)
    chG = add(scal(wB1, Np), pB)
    # (1) the naive exterior product F boxtimes G
    g_naive = wedge(chF, chG)
    a = ann_dim([g_naive], H1T); a_pol = ann_dim([g_naive, th], H1T); a_TD = ann_dim([g_naive, th, Wp, Wm], H1T)
    check("$tag first-order Hodge locus of ch(F boxtimes G) in H^1(T): $a; with theta: $a_pol; inside T D: $a_TD (expected $(expect.naive))",
          (a, a_pol, a_TD) == expect.naive)
    inTD = (ann_dim([wedge(wA1, wB1), th, Wp, Wm], H1T), ann_dim([wedge(wA1, pB), th, Wp, Wm], H1T),
            ann_dim([wedge(pA, wB1), th, Wp, Wm], H1T))
    check("$tag inside T D: loci of omega_1 x omega_1', omega_1 x p', p x omega_1' = $inTD (expected $(expect.inTD))",
          inTD == expect.inTD)
    comp = (ann_dim([wedge(wA1, pB)], H1T), ann_dim([wedge(pA, wB1)], H1T),
            ann_dim([wedge(wA1, wB1)], H1T), ann_dim([wedge(pA, pB)], H1T))
    check("$tag loci in H^1(T) of omega_1 x p', p x omega_1', omega_1 x omega_1', p x p' = $comp (expected $(expect.comp))",
          comp == expect.comp)
    # (2) the twisted difference E_0 = F x G (+) (zeta_* F x zeta^b_* G)[1]
    tw = [(mod(2m + 2mp * b, 3), mod(2m - 2mp * b, 3)) for b in (1, -1)]
    check("$tag twist exponents (on W, on the cross terms) for b = +1, -1: $tw (expected $(expect.tw))", tw == expect.tw)
    b = mod(2m - 2mp, 3) == 0 ? 1 : -1
    check("$tag the chosen twist is nontrivial on W", mod(2m + 2mp * b, 3) != 0)
    wB2 = weil(opB, omB, up, zeta^(2mp * b))
    chG2 = add(scal(wB2, Np), pB)
    g0 = add(wedge(chF, chG), wedge(chF2, chG2), -1.0)
    iWp = sum(bit(2j) for j in 0:2n-1); iWm = sum(bit(2j + 1) for j in 0:2n-1)
    cWp, cWm = get(g0, iWp, C(0)), get(g0, iWm, C(0))
    @printf("ch(E_0): coefficient on omega_+ = %.4f%+.4fim, on omega_- = %.4f%+.4fim\n", real(cWp), imag(cWp), real(cWm), imag(cWm))
    check("$tag ch(E_0): the coefficients on omega_+ and omega_- are conjugate and nonzero",
          abs(cWp - conj(cWm)) < 1e-9 && abs(cWp) > 1e-6)
    cr1 = wedge(opA, omB); cr2 = wedge(omA, opB)       # monomials with coefficient +-1
    x1 = abs(get(g0, first(keys(cr1)), C(0))); x2 = abs(get(g0, first(keys(cr2)), C(0)))
    check("$tag ch(E_0): the cross terms om_+(A) om_-(A'), om_-(A) om_+(A') vanish", x1 < 1e-9 && x2 < 1e-9)
    # (3) cancel omega_i x p', p x omega'_j, then everything in Q[theta_A] (x) Q[theta_B]
    g1 = add(g0, wedge(scal(wA1, N), pB), -1.0)
    g1 = add(g1, wedge(scal(wA2, N), pB), +1.0)
    g1 = add(g1, wedge(pA, scal(wB1, Np)), -1.0)
    g1 = add(g1, wedge(pA, scal(wB2, Np)), +1.0)
    P = hcat([vec_(n, wedge(power(thA, k), power(thB, l))) for k in 0:2m for l in 0:2mp]...)
    v1 = vec_(n, g1)
    coef = P \ v1                      # least squares
    rem = v1 - P * coef
    nw = abs(rem[iWp+1])
    out = copy(rem); out[iWp+1] = 0; out[iWm+1] = 0
    @printf("after cancellations: residual outside span(omega_+, omega_-) = %.2e, |N w| = %.4f\n", norm(out), nw)
    check("$tag after the cancellations ch lies in span(omega_+, omega_-), with N w != 0", norm(out) < 1e-9 && nw > 1e-6)
    g_weil = Elt(UInt32(i - 1) => rem[i] for i in eachindex(rem) if abs(rem[i]) > 1e-9)
    V = [k^j / factorial(j) for k in 0:2m, j in 0:2m]
    dV = det(V)
    check("$tag Vandermonde det (k^j/j!, k,j = 0..$(2m)) = $(round(dV, digits=6)) = 1", abs(dV - 1) < 1e-9)
    # (4) final object: add line bundles e^{k theta}, k = 0, 1, 2, generic multiplicities
    ks = [0, 1, 2]; mult = randn(rng, 3)
    g_final = copy(g_weil)
    for (k, mu) in zip(ks, mult)
        g_final = add(g_final, expo(scal(th, k), 2n), mu)
    end
    cs = [sum(mu * Float64(k)^j / factorial(j) for (k, mu) in zip(ks, mult)) for j in 0:2n]
    rho = hankel_rank(cs, n)
    aH = ann_dim([g_final], H1T)
    A2 = ann_dim([g_final], HT2)
    r = length(HT2) - A2
    println("final ch(E) = N w + sum_k c_k theta^k: rho = $rho, aH = $aH, dim Ann_HT2 = $A2, r = $r")
    check("$tag Hankel rank rho = $rho = 3", rho == 3)
    check("$tag first-order Hodge locus of the final class in H^1(T): aH = $aH = n^2", aH == n * n)
    check("$tag dim Ann_HT2 = $A2 = n^2 (4 - rho)", A2 == n * n * (4 - rho))
    check("$tag r(gamma) = $r = (4 + rho) n^2 - 2n = $(expect.r)", r == (4 + rho) * n * n - 2n && r == expect.r)
    (n=n, TD=TD, Tprod=TA + TB, naive=a, rho=rho, aH=aH, r=r)
end

rng = MersenneTwister(1)
res = [run(rng, 3, 2, (naive=(7, 6, 5), inTD=(5, 5, 5), comp=(11, 13, 11, 13), tw=[(0, 2), (2, 0)], r=57)),
       run(rng, 4, 2, (naive=(8, 8, 8), inTD=(8, 8, 8), comp=(18, 18, 16, 20), tw=[(2, 0), (0, 2)], r=104))]
println("summary: ", join(["n=$(o.n): TD=$(o.TD), Tprod=$(o.Tprod), naive=$(o.naive), rho=$(o.rho), aH=$(o.aH), r=$(o.r)" for o in res], "; "))
println("product_object.jl: $(NPASS[]) checks passed, $(NFAIL[]) failed")
NFAIL[] > 0 && exit(1)
