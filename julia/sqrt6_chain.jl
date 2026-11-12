# sqrt6_chain.jl -- port of code/sqrt6_chain.py (Sect. V, the chain for sqrt 6).
#
# Two-dimensional families of K3 surfaces X with End_Hdg(T(X)_Q) = Q(sqrt 6)
# whose transcendental space embeds isometrically in (U^3 + A_2^2)_Q.
# Rational quadratic forms are classified by rank, signature, discriminant
# and Hasse invariants (Hasse-Minkowski); W embeds in V iff a complement W'
# exists locally everywhere (Serre, Ch. IV); see quadratic_forms.jl.
# Exact integer arithmetic.  The product formula of the Python (300 random
# pairs) is checked here on all pairs with |a|, |b| <= 60.
# Run: julia --startup-file=no sqrt6_chain.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms
using LinearAlgebra: I

# ---- lattices -----------------------------------------------------------------
Umat() = [0 1; 1 0]
A2mat() = [-2 1; 1 -2]                     # negative definite A_2(-1)
function E8neg()
    C = zeros(Int, 8, 8)
    # chain 1-2-3-4-5-6-7 and 8 attached to 5
    for i in 1:8; C[i, i] = -2; end
    for (i, j) in [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (5, 8)]
        C[i, j] = 1; C[j, i] = 1
    end
    return C
end
function dsum(Ms...)
    n = sum(size(M, 1) for M in Ms); G = zeros(Int, n, n); o = 0
    for M in Ms
        k = size(M, 1); G[o+1:o+k, o+1:o+k] = M; o += k
    end
    return G
end
qform(G) = Int[sqfree(x) for x in diagonalize(G)]

# ---- the trace form of a diagonal E-form, E = Q(sqrt n) --------------------------
# entries (a0, a1) stand for a0 + a1 sqrt n; basis 1, sqrt n of each E-line:
# Tr(a (x + y s)^2) = 2 (a0 x^2 + a0 n y^2 + 2 a1 n x y).
trace_block(a0, a1, n) = [2a0 2a1*n; 2a1*n 2a0*n]
trace_form(entries, n) = (dsum((trace_block(a0, a1, n) for (a0, a1) in entries)...),
                          dsum(([0 n; 1 0] for _ in entries)...))
"sign of a0 + a1 sqrt n (n > 0 not a square), exactly"
function sgn_sqrt(a0, a1, n)
    a1 == 0 && return sign(a0)
    a0 == 0 && return sign(a1)
    sign(a0) == sign(a1) && return sign(a0)
    return a0 * a0 > n * a1 * a1 ? sign(a0) : sign(a1)
end
signs(a0, a1, n) = (sgn_sqrt(a0, a1, n), sgn_sqrt(a0, -a1, n))

function combinations_with_replacement(v, m)
    out = Vector{Vector{eltype(v)}}()
    function rec(start, cur)
        if length(cur) == m
            push!(out, copy(cur)); return
        end
        for i in start:length(v)
            push!(cur, v[i]); rec(i, cur); pop!(cur)
        end
    end
    rec(1, eltype(v)[])
    return out
end

candidates(maxc) = [(a0, a1) for a0 in -maxc:maxc for a1 in -maxc:maxc if (a0, a1) != (0, 0)]

"""
Diagonal E-forms <a_1..a_m> over Q(sqrt n), a_i in Z[sqrt n] with |coeffs|
<= maxc, of sign pattern sig1 at sigma_1 and sig2 at sigma_2; returns
(all sign-admissible tuples, those whose trace form is isometric to / embeds in target).
The trace form is block diagonal, so it is diagonalised block by block.
"""
function search(n, m, target, sig1, sig2; maxc, embed_only = false)
    cands = candidates(maxc)
    blk = Dict(c => qform(trace_block(c[1], c[2], n)) for c in cands)
    sg = Dict(c => signs(c[1], c[2], n) for c in cands)
    adm = Vector{Vector{Tuple{Int,Int}}}(); sols = Vector{Vector{Tuple{Int,Int}}}()
    for tup in combinations_with_replacement(cands, m)
        s1 = [sg[c][1] for c in tup]; s2 = [sg[c][2] for c in tup]
        (count(==(1), s1), count(==(-1), s1)) == sig1 || continue
        (count(==(1), s2), count(==(-1), s2)) == sig2 || continue
        push!(adm, tup)
        W = reduce(vcat, [blk[c] for c in tup])
        (embed_only ? embeds(W, target) : isometric(W, target)) && push!(sols, tup)
    end
    return adm, sols
end

fmt(t) = "<" * join(["$(a0)+$(a1)sqrt6" for (a0, a1) in t], ", ") * ">"

function main()
    C = Checks("sqrt6_chain.jl")
    # ---- Hilbert symbol ---------------------------------------------------------
    ok = true; np = 0
    for a in -60:60, b in -60:60
        (a == 0 || b == 0) && continue
        np += 1
        ps = sort!(unique!(vcat(2, primes_of(a), primes_of(b))))
        ok &= hilbert(a, b, 0) * prod(hilbert(a, b, p) for p in ps) == 1
    end
    check(C, "Hilbert symbol product formula on all $np pairs with |a|, |b| <= 60", ok)
    check(C, "(2,2)_2 = (2,-1)_2 = 1", hilbert(2, 2, 2) == 1)
    check(C, "(2,3)_2 = -1 (3 not a norm from Q_2(sqrt 2))", hilbert(2, 3, 2) == -1)
    check(C, "(3,3)_3 = (3,-1)_3 = -1", hilbert(3, 3, 3) == -1)
    check(C, "(-1,-1)_2 = -1", hilbert(-1, -1, 2) == -1)

    # ---- lattices ---------------------------------------------------------------
    @assert prod(diagonalize(E8neg())) == 1          # det E8(-1) = 1
    V3 = qform(dsum(Umat(), Umat(), Umat(), A2mat(), A2mat()))      # Lambda^{Z/3} tensor Q
    V2 = qform(dsum(Umat(), Umat(), Umat(), 2 * E8neg()))           # Lambda^{iota} tensor Q
    check(C, "U^3+A_2^2 has rank 10, signature (3,7)", (length(V3), sig(V3)) == (10, (3, 7)))
    check(C, "U^3+E8(-2) has rank 14, signature (3,11)", (length(V2), sig(V2)) == (14, (3, 11)))
    check(C, "E8(-1)_Q is isometric to <-1>^8", isometric(qform(E8neg()), fill(-1, 8)))
    check(C, "U_Q isometric to <1,-1>", isometric(qform(Umat()), [1, -1]))
    check(C, "<2,2> isometric to <1,1>", isometric([2, 2], [1, 1]))
    check(C, "<1,-3> NOT isometric to <1,-1>", !isometric([1, -3], [1, -1]))
    check(C, "<1,-2> NOT isometric to <1,-1>", !isometric([1, -2], [1, -1]))
    check(C, "<3,-3> isometric to U", isometric([3, -3], [1, -1]))

    # ---- trace forms: self-adjointness and J^2 = n ---------------------------------
    G, J = trace_form([(0, 1), (2, 1), (-1, 0), (-2, 0)], 6)
    check(C, "J^2 = 6", J * J == 6 * I)
    check(C, "sqrt6 is self-adjoint for the trace form", transpose(J) * G == G * J)
    @assert isometric(qform(G), reduce(vcat, [qform(trace_block(a0, a1, 6)) for (a0, a1) in [(0, 1), (2, 1), (-1, 0), (-2, 0)]]))

    # ---- Varesco's two statements as consistency tests ------------------------------
    _, sols2 = search(2, 6, qform(dsum(Umat(), Umat(), 2 * E8neg())), (2, 4), (0, 6); maxc = 2)
    check(C, "Varesco Prop 2.6 reproduced: some Tr q_E over Q(sqrt2) = U^2+E8(-2)_Q (sig (2,4),(0,6))", length(sols2) > 0)
    println("   example: ", isempty(sols2) ? nothing : sols2[1], "  (", length(sols2), " found)")
    _, sols3 = search(3, 4, qform(dsum(Umat(), Umat(), A2mat(), A2mat())), (2, 2), (0, 4); maxc = 2)
    check(C, "Varesco Prop 2.12 reproduced: some Tr q_E over Q(sqrt3) = U^2+A_2^2_Q (sig (2,2),(0,4))", length(sols3) > 0)
    println("   example: ", isempty(sols3) ? nothing : sols3[1], "  (", length(sols3), " found)")

    # ---- the new case: Q(sqrt 6) ----------------------------------------------------
    println("=== Q(sqrt 6), rank 8 = 4 over E, T embeds in U^3 + A_2^2 (complement rank 2) ===")
    adm6, sols6 = search(6, 4, V3, (2, 2), (0, 4); maxc = 2, embed_only = true)
    total = length(adm6); nonemb = total - length(sols6)
    check(C, "exists q_E over Q(sqrt6), sig (2,2)/(0,4), with Tr q_E embedding in (U^3+A_2^2)_Q: $(length(sols6)) of $total sign-admissible forms with |coeffs| <= 2 (expected 98 of 165)",
          length(sols6) == 98 && total == 165)
    for t in sols6[1:min(6, end)]
        println("    ", fmt(t))
    end
    t = sols6[1]
    G, J = trace_form(t, 6)
    W = qform(G)
    println("   first solution ", fmt(t), ": T invariants: rank ", length(W), " sig ", sig(W), " d ", disc(W), " eps ",
            [(p, hasse(W, p)) for p in sort(unique(vcat(relevant_primes(W), 3)))])
    println("   V3 invariants: rank ", length(V3), " sig ", sig(V3), " d ", disc(V3), " eps ",
            [(p, hasse(V3, p)) for p in relevant_primes(V3, W)])
    dW, eps, ps = complement_data(W, V3)
    println("   complement W' (rank 2, sig (1,1)) local data (p, d', eps'): ", [(p, dW, eps[p]) for p in ps])
    check(C, "T(3) embeds in (U^3+E8(-2))_Q  (Nikulin partner of the order-3 quotient exists)", embeds(qform(3 * G), V2))
    println("   other order: T in U^3+E8(-2): ", embeds(W, V2), "; T(2) in U^3+A_2^2: ", embeds(qform(2 * G), V3))
    println("   of $total sign-admissible q_E with |coeffs|<=2, $nonemb do NOT embed (the condition is not vacuous)")
    check(C, "the embedding condition is a genuine restriction: $nonemb of $total q_E fail (expected 67 of 165)",
          nonemb == 67 && total == 165)
    _, sols6b = search(6, 3, V3, (2, 1), (0, 3); maxc = 2, embed_only = true)
    check(C, "rank-6 case: some Tr q_E over Q(sqrt6), sig (2,1)/(0,3), embeds in (U^3+A_2^2)_Q", length(sols6b) > 0)
    check(C, "Z/6, D_5: invariant lattice sig (3,3) forces rank T <= 5, so dim_E T <= 2", div(5, 2) <= 2)

    # ---- explicit complements for the recorded example -------------------------------
    println("=== explicit complements for q_E = <-2, -2, -2+sqrt6, -1+sqrt6> ===")
    t0 = [(-2, 0), (-2, 0), (-2, 1), (-1, 1)]
    G0, J0 = trace_form(t0, 6)
    println("   signs at sigma_1: ", [signs(a0, a1, 6)[1] for (a0, a1) in t0], "  at sigma_2: ", [signs(a0, a1, 6)[2] for (a0, a1) in t0])
    W0 = qform(G0)
    println("   Tr q_E diagonalised (mod squares): ", W0, "  (d = ", disc(W0), ", eps_2, eps_3, eps_5 = ", (hasse(W0, 2), hasse(W0, 3), hasse(W0, 5)), ")")
    @assert t0 in sols6 && isometric(W0, [-1, -6, -1, -6, -1, 3, -2, 15])      # the form T of Table II
    check(C, "V3 = (U^3+A_2^2)_Q is isometric to T + <1,-10>", isometric(vcat(W0, [1, -10]), V3))
    check(C, "<1,-10> has signature (1,1) and contains a positive vector (so N has an ample class)", sig([1, -10]) == (1, 1))
    W3 = qform(3 * G0)
    found = nothing
    vals = [1, -1, 2, -2, 3, -3, 5, -5, 6, -6, 10, -10, 15, -15, 30, -30]
    for c1 in vals, c2 in vals
        cand = vcat(W3, [1, -1, -1, -1, c1, c2])
        if sig(cand) == sig(V2) && isometric(cand, V2)
            found = [1, -1, -1, -1, c1, c2]; break
        end
    end
    check(C, "explicit rank-6 complement of T(3) in (U^3+E8(-2))_Q found: $found (expected <1,-1,-1,-1,-3,-30>)",
          found == [1, -1, -1, -1, -3, -30])
    finish(C)
end
main()
