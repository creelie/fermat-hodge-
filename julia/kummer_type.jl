# kummer_type.jl -- port of code/kummer_type.py: the criterion of
# Proposition V.16 (K3 surfaces of Kummer type over Q) against a direct search.
#
# A rational quadratic space T of signature (2, r-2) embeds isometrically in
# U_Q^3 = H^2(A, Q) of an abelian surface iff r <= 3, or r = 4 and
# eps_p(T) = (-1,-1)_p at every prime p at which d(T) is a square in Q_p, or
# r = 5 and eps_p(T) = (-1,-1)_p at every prime p.  The direct search looks
# for a diagonal complement W in a box and compares T + W with U^3 by rank,
# signature, discriminant and Hasse invariants (quadratic_forms.jl).
# Run: julia --startup-file=no kummer_type.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms

"2 and the primes dividing an entry"
all_primes(diag) = sort!(unique!(vcat(2, [Int.(primes_of(a)) for a in diag]...)))

"Primes at which the local condition of criterion (c) fails."
function failing_primes(diag)
    r = length(diag); d = disc(diag); bad = Int[]
    for p in all_primes(diag)
        if r == 5 && hasse(diag, p) != hilbert(-1, -1, p)
            push!(bad, p)
        end
        if r == 4 && is_square_Qp(d, p) && hasse(diag, p) != hilbert(-1, -1, p)
            push!(bad, p)
        end
    end
    return bad
end

"Criterion (c): does T of signature (2, r-2) embed isometrically in U_Q^3?"
function embeds_in_U3(diag)
    r = length(diag)
    @assert count(>(0), diag) == 2
    r >= 6 && return false
    r <= 3 && return true
    return isempty(failing_primes(diag))
end

const U3 = [1, -1, 1, -1, 1, -1]

"A diagonal W with T + W = U^3 over Q, found by search in the box, or nothing."
function complement(diag; V = U3, box = 30)
    k = length(V) - length(diag)
    coeffs = [c for c in -box:box if c != 0]
    W = fill(coeffs[1], k); idx = ones(Int, k)
    while true
        for i in 1:k; W[i] = coeffs[idx[i]]; end
        isometric(vcat(diag, W), V) && return copy(W)
        i = k                                  # next tuple, last index fastest
        while i >= 1 && idx[i] == length(coeffs); idx[i] = 1; i -= 1; end
        i == 0 && return nothing
        idx[i] += 1
    end
end

function cwr(v, m)                              # combinations with replacement
    out = Vector{Vector{eltype(v)}}()
    function rec(start, cur)
        length(cur) == m && (push!(out, copy(cur)); return)
        for i in start:length(v)
            push!(cur, v[i]); rec(i, cur); pop!(cur)
        end
    end
    rec(1, eltype(v)[])
    return out
end

isprime(n) = n > 1 && all(n % p != 0 for p in 2:isqrt(n))

function main()
    C = Checks("kummer_type.jl")
    # (A) the invariants of U^3
    check(C, "U^3 has discriminant -1", disc(U3) == -1)
    check(C, "U^3 has Hasse invariant (-1,-1)_p at p = 2, 3, 5, 7, 11, 13",
          all(hasse(U3, p) == hilbert(-1, -1, p) for p in (2, 3, 5, 7, 11, 13)))
    check(C, "(-1,-1)_2 = -1 and (-1,-1)_p = 1 for odd p < 50",
          hilbert(-1, -1, 2) == -1 && all(hilbert(-1, -1, p) == 1 for p in 3:49 if isprime(p)))

    # (B) the criterion against the search, ranks 4 and 5
    tests = ["U^2 + <-2>" => [1, -1, 1, -1, -2], "U^2 + <-6>" => [1, -1, 1, -1, -6],
             "U + <2,-2,-2>" => [1, -1, 2, -2, -2], "<2,2,-2,-2,-2>" => [2, 2, -2, -2, -2],
             "<2,6,-2,-2,-2>" => [2, 6, -2, -2, -2], "<2,2,-2,-6,-6>" => [2, 2, -2, -6, -6],
             "U^2 + <-4>" => [1, -1, 1, -1, -4], "U + <2,-2,-6>" => [1, -1, 2, -2, -6],
             "<2,2,-2,-10,-10>" => [2, 2, -2, -10, -10], "<2,2,-2,-2>" => [2, 2, -2, -2],
             "<2,2,-2,-6>" => [2, 2, -2, -6], "<2,6,-2,-2>" => [2, 6, -2, -2],
             "<2,10,-2,-2>" => [2, 10, -2, -2], "U + <2,-6>" => [1, -1, 2, -6]]
    agree = 0
    results = Dict{String,Any}()
    for (name, T) in tests
        crit = embeds_in_U3(T)
        W = complement(T)
        results[name] = (crit, W)
        agree += crit == (W !== nothing)
        println("      ", rpad(name, 18), " rank ", length(T), "  criterion=", rpad(crit, 5), "  complement=", W)
    end
    check(C, "criterion (c) agrees with the search on $agree of $(length(tests)) spaces", agree == length(tests))
    check(C, "U^2 + <-2> and U + <2,-2,-2> are of Kummer type",
          results["U^2 + <-2>"][1] && results["U + <2,-2,-2>"][1])
    check(C, "<2,2,-2,-6,-6> and <2,6,-2,-2,-2> are not, and fail at p = 2 and p = 3",
          failing_primes([2, 2, -2, -6, -6]) == [2, 3] && failing_primes([2, 6, -2, -2, -2]) == [2, 3])
    check(C, "every space of rank 4 in the list is of Kummer type",
          all(results[n][1] for (n, T) in tests if length(T) == 4))
    T4 = [2, 2, -6, -6]
    check(C, "<2,2,-6,-6> (rank 4, d = 1) fails at p = 2 and p = 3, and the search finds no complement",
          failing_primes(T4) == [2, 3] && complement(T4) === nothing)
    # counts over a box of coefficients: how often the condition holds
    vals = [1, 2, 3, 5, 6, 10, 15, 30]
    c4 = Dict(true => 0, false => 0)
    for (a, b) in cwr(vals, 2), (c, d) in cwr(vals, 2)
        c4[embeds_in_U3([a, b, -c, -d])] += 1
    end
    c5 = Dict(true => 0, false => 0); pairs = true
    for (a, b) in cwr(vals, 2), (c, d, e) in cwr(vals, 3)
        T = [a, b, -c, -d, -e]
        c5[embeds_in_U3(T)] += 1
        pairs &= iseven(length(failing_primes(T)))
    end
    println("      rank 4 over the box: $(c4[true]) of Kummer type, $(c4[false]) not; rank 5: $(c5[true]) and $(c5[false])")
    check(C, "rank 4: 1084 of 1296 diagonal spaces over the box embed; rank 5: 1304 of 4320",
          (c4[true], c4[false], c5[true], c5[false]) == (1084, 212, 1304, 3016))
    check(C, "the primes at which (c) fails come in pairs (product formula) for every space of the box", pairs)
    check(C, "rank 6 of signature (2,4) never embeds (signature)", !embeds_in_U3([1, -1, 1, -1, -2, -2]))
    # the criterion is the embedding test of Hasse-Minkowski (quadratic_forms.embeds) on the whole box
    @assert all(embeds_in_U3([a, b, -c, -d]) == embeds([a, b, -c, -d], U3) for (a, b) in cwr(vals, 2) for (c, d) in cwr(vals, 2))
    @assert all(embeds_in_U3([a, b, -c, -d, -e]) == embeds([a, b, -c, -d, -e], U3) for (a, b) in cwr(vals, 2) for (c, d, e) in cwr(vals, 3))

    # (C) discriminants mod squares: d(T) = -d(NS) for a primitive sublattice of the K3 lattice (d = -1)
    dU, dA1, dA4, dA6, dD4 = -1, -2, 5, 7, 4        # negative definite root lattices
    dNS5 = dU * dA4 * dA1^2 * dD4^2                 # U + A4 + A1^2 + D4^2
    dNS7 = dU * dA6 * dD4^2                         # U + A6 + D4^2
    dT5, dT7 = sqfree(-1 // dNS5), sqfree(-1 // dNS7)
    check(C, "Fricke N = 5: d(T) = 5 mod squares", dT5 == 5)
    check(C, "Fricke N = 7: d(T) = 7 mod squares", dT7 == 7)
    dSix = disc([1, -1, 1, -1, -2, -2])             # six lines, U_Q^2 + <-2>^2
    dILP = disc([1, -1, 1, -1, -6, -2])             # 15-nodal, U_Q^2 + <-6> + <-2>
    check(C, "Varesco's families: d(T) = 1 and 3 mod squares", (dSix, dILP) == (1, 3))
    check(C, "the four discriminant classes 1, 3, 5, 7 are distinct", length(Set([dSix, dILP, dT5, dT7])) == 4)
    finish(C)
end
main()
