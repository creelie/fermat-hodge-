# convolution_checks.jl -- port of code/convolution_checks.py.
# Numerical checks in the exterior-algebra model of H^*(A x A') (conventions of
# product_object.jl) at (m,m') = (2,1), (2,2):
#  (A) the rank of v -> v _| theta_A on T D_{n,n} equals the number
#      n^2 - m^2 - m'^2 of mixed directions (4 and 8);
#  (B) r(gamma) = 57 and 104, and under the orthogonality hypotheses V', V'', V
#      the common annihilator of the summands exceeds r by the mixed directions;
#  (C) Hankel rank 3 of the character of a middle-dimensional subvariety;
#  (D) tr(upper triangular x strictly upper triangular block matrix) = 0.
# As in the Python program the ranks are numerical (singular values with
# relative tolerance 1e-7, complex double precision, generic data from a
# fixed seed); every rank is an integer.
# Run: julia --startup-file=no convolution_checks.jl
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
    opA, omA, opB, omB = om(IA, true), om(IA, false), om(IB, true), om(IB, false)
    H1T = h1T_ops(n); HT2 = ht2_ops(n)
    println("=== $tag: A (Weil $(2m)-fold) x A' (Weil $(2mp)-fold); dim H^1(T) = $(length(H1T)), dim HT^2 = $(length(HT2)) ===")
    Wp, Wm = wedge(opA, opB), wedge(omA, omB)
    # T D_{n,n} in H^1(T): left null space of the contraction into theta, W_+, W_-
    M = cmat([th, Wp, Wm], H1T)
    F = svd(M; full=true)
    rk = count(>(1e-7 * F.S[1]), F.S)
    TD = F.U[:, rk+1:end]'
    check("$tag dim T D_(n,n) = $(size(TD, 1)) = n^2", size(TD, 1) == n * n)
    inA(o) = (o[1][2] ÷ 2 in IA) && (o[2][2] ÷ 2 in IA)
    inB(o) = (o[1][2] ÷ 2 in IB) && (o[2][2] ÷ 2 in IB)
    blockA = [o for o in H1T if inA(o)]; blockB = [o for o in H1T if inB(o)]
    # (A) rank of v -> v _| theta_A on T D
    r_thA = rank_(TD * cmat([thA], H1T))
    n_mixed = n * n - ann_dim([thA, opA, omA], blockA) - ann_dim([thB, opB, omB], blockB)
    check("$tag (A) rank of (v -> v _| theta_A) on T D = $r_thA = number of mixed directions n^2-m^2-m'^2 = $n_mixed = $(expect.mixed)",
          r_thA == n_mixed && n_mixed == expect.mixed && n_mixed == n * n - m * m - mp * mp)
    # classes of the pieces (twist by K = Q(zeta_3))
    u, up = crandn(rng), crandn(rng)
    weil(opl, oml, uu, lam) = add(scal(opl, lam * uu), scal(oml, conj(lam * uu)))
    wA1, wA2 = weil(opA, omA, u, 1), weil(opA, omA, u, zeta^(2m))
    b = mod(2m - 2mp, 3) == 0 ? 1 : -1
    wB1, wB2 = weil(opB, omB, up, 1), weil(opB, omB, up, zeta^(2mp * b))
    pA = [Elt(), Elt()]; pB = [Elt(), Elt()]
    for i in 1:2
        for k in 0:2m
            pA[i] = add(pA[i], power(thA, k), randn(rng))
        end
        for k in 0:2mp
            pB[i] = add(pB[i], power(thB, k), randn(rng))
        end
    end
    chF = [add(wA1, pA[1]), add(wA2, pA[2])]
    chG = [add(wB1, pB[1]), add(wB2, pB[2])]
    a = Dict((1, 1) => 1.0, (2, 2) => -1.0)     # twisted difference
    E_FG = Elt(); E_FLp = Elt(); E_LGp = Elt()
    for ((i, j), aij) in a
        E_FG = add(E_FG, wedge(chF[i], chG[j]), aij)
    end
    for i in 1:2
        qpi = Elt()
        for j in 1:2
            haskey(a, (i, j)) && (qpi = add(qpi, pB[j], a[(i, j)]))
        end
        E_FLp = add(E_FLp, wedge(chF[i], qpi), -1.0)
    end
    for j in 1:2
        qj = Elt()
        for i in 1:2
            haskey(a, (i, j)) && (qj = add(qj, pA[i], a[(i, j)]))
        end
        E_LGp = add(E_LGp, wedge(qj, chG[j]), -1.0)
    end
    partial = add(add(E_FG, E_FLp), E_LGp)
    v0 = vec_(n, partial)
    iWp = sum(bit(2j) for j in 0:2n-1); iWm = sum(bit(2j + 1) for j in 0:2n-1)
    polyAB = hcat([vec_(n, wedge(power(thA, k), power(thB, l))) for k in 0:2m for l in 0:2mp]...)
    coef = polyAB \ v0
    rem = v0 - polyAB * coef
    nw = abs(rem[iWp+1]); out = copy(rem); out[iWp+1] = 0; out[iWm+1] = 0
    @printf("(B) residual outside span(omega_+, omega_-) + Q[th_A] x Q[th_A'] = %.1e, |N w| = %.3f\n", norm(out), nw)
    check("$tag (B) ch(E_FG)+ch(E_FL')+ch(E_LG') = N w + s_2, s_2 in Q[th_A] x Q[th_A'], N w != 0", norm(out) < 1e-9 && nw > 1e-6)
    mult = randn(rng, 3)
    E_LLp = Elt()
    for k in 0:2m, l in 0:2mp
        E_LLp = add(E_LLp, wedge(power(thA, k), power(thB, l)), -coef[k*(2mp+1)+l+1])
    end
    for (k, mu) in zip((0, 1, 2), mult)
        E_LLp = add(E_LLp, expo(scal(th, k), 2n), mu)
    end
    gamma = add(partial, E_LLp)
    cs = [sum(mu * Float64(k)^j / factorial(j) for (k, mu) in zip((0, 1, 2), mult)) for j in 0:2n]
    rho = hankel_rank(cs, n)
    annG = ann_dim([gamma], HT2); r = length(HT2) - annG
    check("$tag (B) gamma = ch(E): rho = $rho = 3, dim Ann_HT2(gamma) = $annG = n^2, r(gamma) = $r = (4+rho)n^2-2n = $(expect.r)",
          rho == 3 && annG == n * n && r == (4 + rho) * n * n - 2n && r == expect.r)
    hyps = [("V' (Ext(F_i,L^l)=0 both ways): E_F (+) E_rest", [add(E_FG, E_FLp), add(E_LGp, E_LLp)]),
            ("V'' (Ext(G'_j,L'^k)=0 both ways): E_G (+) E_rest'", [add(E_FG, E_LGp), add(E_FLp, E_LLp)]),
            ("V (all cross Ext zero): four summands", [E_FG, E_FLp, E_LGp, E_LLp])]
    for (h, (name, parts)) in enumerate(hyps)
        ranks = [contraction_rank(g, HT2) for g in parts]
        common = ann_dim(parts, HT2)
        ex = length(HT2) - common - r
        check("$tag (B) $name: contraction ranks $ranks (expected $(expect.ranks[h])), sum $(sum(ranks)); " *
              "dim HT^2 - dim(common annihilator) = $(length(HT2)-common), excess over r = $ex = mixed directions",
              ranks == expect.ranks[h] && ex == n_mixed)
    end
    (n=n, r=r, rho=rho, mixed=n_mixed)
end

function prym_shape(rng)
    println("=== (C) the character of a middle-dimensional subvariety Y on a very general Weil 2n-fold ===")
    for n in (2, 3, 4, 5)
        rhos = Int[]
        for trial in 0:2
            cs = vcat(zeros(n), [1.0 + randn(rng)], randn(rng, n))
            trial == 2 && (cs = vcat(zeros(n), [1.0], zeros(n)))      # ch(O_Y) = [Y] only
            push!(rhos, hankel_rank(cs, n))
        end
        check("(C) n=$n: c_0..c_$(n-1) = 0, c_n != 0 gives rho = $rhos = 3 (two generic tails, one zero tail), r = 7n^2-2n = $(7n*n-2n)",
              all(==(3), rhos))
        check("(C) n=$n: 7n^2-2n = C(2n,2) + 3n^2 + C(2n,2) = $(binomial(2n,2)) + $(3n*n) + $(binomial(2n,2))",
              7n * n - 2n == 2 * binomial(2n, 2) + 3n * n)
    end
end

function trace_check(rng)
    println("=== (D) trace of (upper triangular) x (strictly upper triangular) block matrix vanishes ===")
    sizes = [2, 3, 1, 4]; N = length(sizes); off = cumsum(vcat(0, sizes))
    function blocks(strict)
        M = zeros(C, off[end], off[end])
        for a in 1:N, b in (strict ? a + 1 : a):N
            M[off[a]+1:off[a+1], off[b]+1:off[b+1]] = randn(rng, sizes[a], sizes[b]) + im * randn(rng, sizes[a], sizes[b])
        end
        M
    end
    U = blocks(false); S = blocks(true)
    for p in 0:3
        t1 = abs(tr(U^p * S)); t2 = abs(tr(S * U^p))
        check("(D) tr(U^$p S) = $(@sprintf("%.1e", t1)), tr(S U^$p) = $(@sprintf("%.1e", t2)): both zero", t1 < 1e-9 && t2 < 1e-9)
    end
end

# seed: MersenneTwister(7) happens to draw the multiplicity -3.0e-6 for the trivial
# line bundle at n = 4, a class within the tolerance of Hankel rank 2; seed 11 is generic.
rng = MersenneTwister(11)
out = [run(rng, 3, 2, (r=57, mixed=4, ranks=[[58, 55], [46, 59], [58, 58, 52, 53]])),
       run(rng, 4, 2, (r=104, mixed=8, ranks=[[100, 106], [100, 106], [112, 106, 106, 100]]))]
prym_shape(rng); trace_check(rng)
println("summary: ", join(["n=$(o.n): r=$(o.r), rho=$(o.rho), mixed=$(o.mixed)" for o in out], "; "))
println("convolution_checks.jl: $(NPASS[]) checks passed, $(NFAIL[]) failed")
NFAIL[] > 0 && exit(1)
