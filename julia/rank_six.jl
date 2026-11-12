# rank_six.jl -- port of rounds/r1-F3/qf.py, rm_rank6.py and powers_rho.py.
#
# (0) self-tests of the Hilbert symbol (qf.py);
# (A) Theorem A (rm_rank6.py): for the 305 squarefree d in [2,500],
#     T_d = Tr_{E/Q} <sqrt d, sqrt d, -1/2>, E = Q(sqrt d): multiplication M by
#     sqrt d has M^2 = d and is self-adjoint; T_d = U^2 + <-1> + <-d> over Q;
#     the two eigenspaces of M have signatures (2,1) and (0,3); T_d embeds in
#     U^3 + <-1> = Lambda_Kum3(2)_Q, T_d + <d> = U^3 + <-1>, and
#     eps_p(T_d) = (-1,d)_p at every prime; L_d = U^2 + <-4> + <-4d> has L_d (x) Q = T_d.
#     Which d <= 60 are reached by the two older families; the four known
#     families against the scalings 1, 2, 3, 6.
# (B, C) Theorems B, C (powers_rho.py): which T of rank <= 6 have
#     T(lam) -> U^3 + <-1> for lam in {1, 2, 3, 6}; the rank-5 criterion
#     eps_p(T) = (-1,-1)_p where -d(T) is a p-adic square (110976 forms, 6526
#     with no lam); the rank-6 criterion eps_p(T)(lam,-d)_p = (-1,d)_p (5880
#     forms x 4 scalings, 2455 covered, 3425 not covered).
# Exact integer arithmetic.  Where the Python draws random samples (3000
# pairs for the product formula, 2000 forms of rank 4) the full grids are
# used; the eigenspace signatures are decided exactly (the Python uses floats).
# Run: julia --startup-file=no rank_six.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms
using LinearAlgebra: I

const U = [1, -1]
const V_FLO = vcat(U, U, U, [-1])                 # Lambda_Kum3(2) (x) Q = (U^3 + <-8>)(2) ~ U^3 + <-1>
const V2 = vcat(U, U, U, fill(-1, 8))             # (U^3 + E8(-2)) (x) Q
const V3 = vcat(U, U, U, [-2, -6, -2, -6])        # (U + U(3)^2 + A2^2) (x) Q
const LAMS = (1, 2, 3, 6)

function block_diag(blocks)
    n = sum(size(b, 1) for b in blocks); M = zeros(Int, n, n); o = 0
    for b in blocks
        k = size(b, 1); M[o+1:o+k, o+1:o+k] = b; o += k
    end
    return M
end
# W = <sqrt d, sqrt d, -1/2> over E = Q(sqrt d); basis (1, sqrt d) of each E-line.
# Tr(alpha x y): alpha = sqrt d -> [0 2d; 2d 0]; alpha = -1/2 -> [-1 0; 0 -d]
gram_and_M(d) = (block_diag([[0 2d; 2d 0], [0 2d; 2d 0], [-1 0; 0 -d]]),
                 block_diag([[0 d; 1 0] for _ in 1:3]))       # multiplication by sqrt d
function diag_of_binary(g)
    a, b, c = g[1, 1], g[1, 2], g[2, 2]
    a != 0 && return [a, a * (a * c - b * b)]
    return c == 0 ? [1, -1] : [c, c * (a * c - b * b)]         # a = c = 0: hyperbolic
end
"sign of x + y sqrt d, exactly"
function sgn_sqrt(x, y, d)
    y == 0 && return sign(x)
    x == 0 && return sign(y)
    sign(x) == sign(y) && return sign(x)
    return x * x > d * y * y ? sign(x) : sign(y)
end
flo(T) = [l for l in LAMS if embeds(scale(T, l), V_FLO)]
"necessary condition for Tr W ~ Tfam, W over Q(sqrt d) of sign type ((2,1),(0,3)): (disc d, d)_p = 1 for all p"
function reach(Tfam, d)
    x = disc(Tfam) * d
    return all(hilbert(x, d, p) == 1 for p in vcat(0, 2, primes_of(x), primes_of(d)))
end

function main()
    C = Checks("rank_six.jl")
    # ---- (0) qf.py self-tests ------------------------------------------------------
    ok = true; np = 0
    for a in -400:400, b in -400:400
        (a == 0 || b == 0) && continue
        np += 1
        ps = vcat(0, sort!(unique!(vcat(2, primes_of(a), primes_of(b)))))
        pr = 1
        for p in ps
            h = hilbert(a, b, p); pr *= h
            ok &= hilbert(a, -a, p) == 1 && h == hilbert(b, a, p)
        end
        ok &= pr == 1
    end
    check(C, "product formula, (a,-a)_p = 1 and symmetry on all $np pairs with 0 < |a|, |b| <= 400", ok)
    check(C, "(a,1-a)_p = 1 at the real place, 2 and the primes of a(1-a), for a != 0, 1 with |a| <= 400",
          all(hilbert(a, 1 - a, p) == 1 for a in -400:400 if a != 0 && a != 1 for p in vcat(0, 2, primes_of(a), primes_of(1 - a))))
    check(C, "(-1,-1)_2 = -1, (-1,-1)_3 = 1, (2,6)_3 = -1", hilbert(-1, -1, 2) == -1 && hilbert(-1, -1, 3) == 1 && hilbert(2, 6, 3) == -1)
    check(C, "V3 = U^3 + A_2^2: d = -1, eps_2 = 1, eps_3 = -1", disc(V3) == -1 && hasse(V3, 2) == 1 && hasse(V3, 3) == -1)
    check(C, "V2 = U^3 + E8(-2): d = -1, eps_2 = -1, eps_3 = 1", disc(V2) == -1 && hasse(V2, 2) == -1 && hasse(V2, 3) == 1)

    # ---- (A) Theorem A (rm_rank6.py) ------------------------------------------------
    ds = [d for d in 2:500 if sqfree(d) == d]
    check(C, "there are 305 squarefree d in [2,500]", length(ds) == 305)
    okM = okSA = okT = okSig = okEmb = okSum = okEps = okL = true
    for d in ds
        G, M = gram_and_M(d)
        okM &= M * M == d * I
        okSA &= transpose(M) * G == G * M
        T = reduce(vcat, [diag_of_binary(G[2i-1:2i, 2i-1:2i]) for i in 1:3])
        Td = vcat(U, U, [-1, -d])
        okT &= isometric(T, Td) && sig(T) == (2, 4) && disc(T) == d && isometric(Int[sqfree(x) for x in diagonalize(G)], Td)
        # eigenvector (+-sqrt d, 1) of each block: value g11 d + g22 +- 2 g12 sqrt d
        for (sgn, want) in ((1, (2, 1)), (-1, (0, 3)))
            vals = [sgn_sqrt(G[2i-1, 2i-1] * d + G[2i, 2i], sgn * 2 * G[2i-1, 2i], d) for i in 1:3]
            okSig &= (count(>(0), vals), count(<(0), vals)) == want
        end
        okEmb &= embeds(Td, V_FLO)
        okSum &= isometric(vcat(Td, d), V_FLO)
        okEps &= all(hasse(Td, p) == hilbert(-1, d, p) for p in relevant_primes(Td))
        okL &= isometric(vcat(U, U, [-4, -4d]), Td)
    end
    check(C, "M^2 = d for the 305 d", okM)
    check(C, "M is self-adjoint, M^T G = G M, for the 305 d", okSA)
    check(C, "T_d = U^2 + <-1> + <-d> over Q, of signature (2,4) and discriminant d, for the 305 d", okT)
    check(C, "the eigenspaces of M have signatures (2,1) and (0,3) for the 305 d", okSig)
    check(C, "T_d embeds in U^3 + <-1> for the 305 d", okEmb)
    check(C, "T_d + <d> = U^3 + <-1> over Q for the 305 d", okSum)
    check(C, "eps_p(T_d) = (-1,d)_p at every relevant prime for the 305 d", okEps)
    check(C, "L_d = U^2 + <-4> + <-4d> has L_d (x) Q = T_d for the 305 d", okL)

    six = vcat(U, U, [-2, -2]); ilp = vcat(U, U, [-6, -2])
    r6 = [d for d in ds if d <= 60 && reach(six, d)]
    ri = [d for d in ds if d <= 60 && reach(ilp, d)]
    none = [d for d in ds if d <= 60 && !(d in r6) && !(d in ri)]
    println("necessary discriminant condition, d<=60: six-lines family (disc 1): ", r6)
    println("necessary discriminant condition, d<=60: 15-nodal family (disc 3):   ", ri)
    println("d<=60 excluded from both older families (new via T_d): ", none)
    check(C, "d <= 60 allowed for the six-lines family: 2, 5, 10, 13, 17, 26, 29, 34, 37, 41, 53, 58",
          r6 == [2, 5, 10, 13, 17, 26, 29, 34, 37, 41, 53, 58])
    check(C, "d <= 60 allowed for the 15-nodal family: 3, 7, 13, 19, 21, 31, 37, 39, 43, 57",
          ri == [3, 7, 13, 19, 21, 31, 37, 39, 43, 57])
    check(C, "d <= 60 excluded from both: 6, 11, 14, 15, 22, 23, 30, 33, 35, 38, 42, 46, 47, 51, 55, 59",
          none == [6, 11, 14, 15, 22, 23, 30, 33, 35, 38, 42, 46, 47, 51, 55, 59])
    check(C, "sqrt 5, 7, 10, 14, 15, 21: six-lines T F T F F F; 15-nodal F T F F F T",
          [reach(six, d) for d in (5, 7, 10, 14, 15, 21)] == [true, false, true, false, false, false] &&
          [reach(ilp, d) for d in (5, 7, 10, 14, 15, 21)] == [false, true, false, false, false, true])
    fam = ["six lines U^2+<-2>^2" => (six, [1, 2]), "15 nodes U^2+<-6>+<-2>" => (ilp, [2, 6]),
           "Fricke N=5 U^2+<-1>+<-5>" => (vcat(U, U, [-1, -5]), [1, 6]), "Fricke N=7 U^2+<-1>+<-7>" => (vcat(U, U, [-1, -7]), [1, 2])]
    for (n, (T, want)) in fam
        got = flo(T)
        println("  ", n, ": T(lam) embeds in U^3+<-1> for lam in ", got)
        check(C, "$n: T(lam) embeds in U^3+<-1> exactly for lam in $want among 1, 2, 3, 6; criterion eps_p(T) = (-1,d(T))_p agrees at lam = 1",
              got == want && embeds(T, V_FLO) == all(hasse(T, p) == hilbert(-1, disc(T), p) for p in relevant_primes(T)))
    end

    # ---- (B, C) Theorems B, C (powers_rho.py) ----------------------------------------
    check(C, "signature (2,k), k = 0..4: embeds in V2 (rank 14) and V3 (rank 10)",
          all(embeds(vcat([1, 1], fill(-1, k)), V2) && embeds(vcat([1, 1], fill(-1, k)), V3) for k in 0:4))
    KUM = vcat(U, U, U)
    examples = [([1, -1, 1, -1, -2], true, [1, 2, 3, 6]), ([1, -1, 2, -2, -2], true, [1, 2, 3, 6]), ([2, 2, -2, -2], true, [1, 2, 3, 6]),
                ([2, 2, -6, -6], false, [1, 2, 3, 6]), ([2, 2, -2, -6, -6], false, [1, 3, 6]), ([2, 6, -2, -2, -2], false, [1, 2, 3])]
    for (T, kum, lams) in examples
        check(C, "T = $T: Kummer type (T -> U^3): $kum; T(lam) -> U^3+<-1> for lam in $lams", embeds(T, KUM) == kum && flo(T) == lams)
    end
    # rank 4: every T of signature (2,2) embeds (rank difference 3)
    cnt = 0; ok = true
    for a in 1:60, b in a:60, c in 1:60, e in c:60
        ok &= embeds([a, b, -c, -e], V_FLO); cnt += 1
    end
    check(C, "rank 4: all $cnt forms <a,b,-c,-e>, 1 <= a <= b <= 60, 1 <= c <= e <= 60, embed in U^3+<-1>", ok)
    # rank 5: eps_p(T) = (-1,-1)_p at all p where -disc(T) is a p-adic square
    crit5(T) = (d = disc(T); all(hasse(T, p) == hilbert(-1, -1, p) for p in relevant_primes(T) if is_square_Qp(-d, p)))
    fails5 = Vector{Vector{Int}}(); tot = 0; ok = true
    rng = [1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 21, 23, 46, 47, 69]
    for a in rng, b in rng, c in rng, e in rng, f in rng
        (a > b || c > e || e > f) && continue
        T = [a, b, -c, -e, -f]; tot += 1
        ok &= embeds(T, V_FLO) == crit5(T)
        isempty(flo(T)) && push!(fails5, T)
    end
    println("rank 5: $tot diagonal forms; with no lam in {1,2,3,6}: $(length(fails5)); first few: $(fails5[1:4])")
    check(C, "rank 5: criterion eps_p(T) = (-1,-1)_p at p with -d(T) in Q_p^2 confirmed on $tot diagonal forms (expected 110976)", ok && tot == 110976)
    check(C, "rank 5: $(length(fails5)) forms with no lam in {1,2,3,6} (expected 6526), the first four <1,1,-1,-23,-23>, <1,1,-1,-23,-46>, <1,1,-1,-23,-69>, <1,1,-1,-46,-46>",
          length(fails5) == 6526 && fails5[1:4] == [[1, 1, -1, -23, -23], [1, 1, -1, -23, -46], [1, 1, -1, -23, -69], [1, 1, -1, -46, -46]])
    badp(T) = (d = disc(T); [l => [p for p in relevant_primes(T) if is_square_Qp(-d * l, p) && hasse(T, p) != hilbert(-1, -1, p)] for l in LAMS])
    println("        ", fails5[1], " disc ", disc(fails5[1]), " bad primes per lam: ", badp(fails5[1]))
    println("        ", fails5[2], " disc ", disc(fails5[2]), " bad primes per lam: ", badp(fails5[2]))
    check(C, "<1,1,-1,-23,-23>: disc -1, bad primes 1: [2,23], 2: [23], 3: [23], 6: [23]; <1,1,-1,-23,-46>: disc -2, bad primes 1: [23], 2: [2,23], 3: [23], 6: [23]",
          disc(fails5[1]) == -1 && badp(fails5[1]) == [1 => [2, 23], 2 => [23], 3 => [23], 6 => [23]] &&
          disc(fails5[2]) == -2 && badp(fails5[2]) == [1 => [23], 2 => [2, 23], 3 => [23], 6 => [23]])
    # rank 6: eps_p(T) = (-1,disc)_p at all p; scaling changes eps_p by (lam,-disc)_p
    crit6(T, l) = (d = disc(T); all(hasse(T, p) * hilbert(l, -d, p) == hilbert(-1, d, p) for p in sort!(unique!(vcat(relevant_primes(T), [2, 3])))))
    fails6 = Vector{Vector{Int}}(); tot = 0; ok = true
    rng6 = [1, 2, 3, 5, 7, 11, 23]
    for a in rng6, b in rng6
        a > b && continue
        for c in rng6, e in rng6, f in rng6, g in rng6
            (c <= e <= f <= g) || continue
            T = [a, b, -c, -e, -f, -g]; tot += 1
            for l in LAMS; ok &= embeds(scale(T, l), V_FLO) == crit6(T, l); end
            isempty(flo(T)) && push!(fails6, T)
        end
    end
    println("rank 6: $tot diagonal forms; covered by some lam: $(tot - length(fails6)), not covered: $(length(fails6)); e.g. $(fails6[1:3])")
    check(C, "rank 6: criterion eps_p(T)(lam,-d)_p = (-1,d)_p confirmed on $tot diagonal forms x 4 scalings (expected 5880)", ok && tot == 5880)
    check(C, "rank 6: $(tot - length(fails6)) covered by some lam, $(length(fails6)) not covered (expected 2455 and 3425), the first three <1,1,-1,-1,-5,-23>, <1,1,-1,-1,-7,-7>, <1,1,-1,-1,-7,-23>",
          tot - length(fails6) == 2455 && length(fails6) == 3425 &&
          fails6[1:3] == [[1, 1, -1, -1, -5, -23], [1, 1, -1, -1, -7, -7], [1, 1, -1, -1, -7, -23]])
    finish(C)
end
main()
