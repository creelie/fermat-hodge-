# clifford_check.jl -- the trace form of a hermitian form (Theorem thm:traceform).
# K = Q(sqrt(-d)), H = <a_1,...,a_2n> diagonal hermitian of signature (n,n).
# Its trace form is q_H = <1,d> (x) <a_1,...,a_2n>.  We check on random forms
#   q_H hyperbolic over Q  <=>  (-d, (-1)^n det H)_v = 1 at every place v
#                          <=>  (-1)^n det H is a norm from K,
# testing hyperbolicity by Hasse-Minkowski (dimension, signature,
# discriminant, Hasse invariants at all relevant primes), and that a binary
# form <b_1,b_2> of signature (1,1) is isotropic iff -b_1 b_2 is a norm.
# Run: julia --startup-file=no clifford_check.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms
using Random

hyperbolic(m) = vcat([[1, -1] for _ in 1:div(m, 2)]...)
isnorm(x, d, ps) = all(hilbert(x, -d, p) == 1 for p in vcat(ps, [0]))

function main()
    C = Checks("clifford_check.jl")
    rng = MersenneTwister(20261113)
    vals = [1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 21]
    agree = true; nsplit = 0; nnon = 0; total = 0
    for d in [1, 2, 3, 5, 6, 7, 10, 11, 13, 15], n in 1:4, trial in 1:60
        a = vcat([rand(rng, vals) for _ in 1:n], [-rand(rng, vals) for _ in 1:n])
        detH = prod(BigInt.(a))
        qH = vcat([[x, d * x] for x in a]...)
        ps = sort!(unique!(vcat(relevant_primes(qH, [d]), Int.(primes_of(sqfree(detH))))))
        hyp = isometric(qH, hyperbolic(4n))
        split = isnorm((-1)^n * detH, d, ps)
        agree &= (hyp == split)
        split ? (nsplit += 1) : (nnon += 1); total += 1
    end
    check(C, "$total random forms (d, n <= 4): q_H hyperbolic <=> (-d,(-1)^n det H)_v = 1 for all v ($nsplit split, $nnon non-split)", agree && nsplit > 0 && nnon > 0)
    ok = true
    for d in [1, 2, 3, 5, 7], b1 in [1, 2, 3, 5, 6, 7], b2 in [-1, -2, -3, -5, -6, -7]
        q4 = [b1, d * b1, b2, d * b2]
        ps = relevant_primes(q4, [d])
        ok &= isometric(q4, hyperbolic(4)) == isnorm(-b1 * b2, d, ps)
    end
    check(C, "180 binary forms <b1,b2> of signature (1,1): trace form hyperbolic <=> -b1 b2 a norm from K", ok)
    # Witt index n-1 for non-split forms: q_H = (n-1) hyperbolic planes + an anisotropic 4-dim form
    ok = true; tested = 0
    for d in [1, 2, 3, 5, 7], n in 2:4, trial in 1:20
        a = vcat([rand(rng, vals) for _ in 1:n], [-rand(rng, vals) for _ in 1:n])
        detH = prod(BigInt.(a))
        qH = vcat([[x, d * x] for x in a]...)
        ps = sort!(unique!(vcat(relevant_primes(qH, [d]), Int.(primes_of(sqfree(detH))))))
        isnorm((-1)^n * detH, d, ps) && continue
        b = (-1)^(n - 1) * detH                  # H = <1,-1>^(n-1) + <1, b>
        q4 = [1, d, sqfree(b), sqfree(d * b)]
        rest = vcat(hyperbolic(4 * n - 4), q4)
        ok &= isometric(qH, rest)
        ok &= !isnorm(-sqfree(b), d, ps)       # <1,b> anisotropic
        tested += 1
    end
    check(C, "$tested non-split forms: q_H = (2n-2) hyperbolic planes + anisotropic <1,d>(x)<1,b>, b = (-1)^(n-1) det H (Witt index 2n-2 of q_H)", ok && tested > 0)
    finish(C)
end
main()
