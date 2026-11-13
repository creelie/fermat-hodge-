# qm_disc.jl -- the discriminant of QM abelian varieties of Weil type (Theorem thm:qmloci(ii)).
# B = (-d, beta) with basis 1, i, j, ij (i^2 = -d, j^2 = beta, ij = -ji); K = Q(i)
# acts on V = B^m by left multiplication; tau(x) = i^{-1} xbar i;
# E_nu(x, y) = trd(sum_ab x_a nu_ab conj(y_b) i) for nu hermitian (nu_ba = conj nu_ab,
# nu_aa rational).  For random nu we check: E alternating, E(bx, y) = E(x, tau(b) y),
# H(x, y) = E(ix, y) + i E(x, y) K-hermitian of signature (m, m), and
# det_K H / (-beta)^m a norm from K^x.  Exact rational arithmetic.
# Run: julia --startup-file=no qm_disc.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms
using Random

const R = Rational{BigInt}
qmul(x, y, d, be) = (x[1]*y[1] - d*x[2]*y[2] + be*x[3]*y[3] + d*be*x[4]*y[4],
                     x[1]*y[2] + x[2]*y[1] - be*x[3]*y[4] + be*x[4]*y[3],
                     x[1]*y[3] + x[3]*y[1] - d*x[2]*y[4] + d*x[4]*y[2],
                     x[1]*y[4] + x[4]*y[1] + x[2]*y[3] - x[3]*y[2])
qconj(x) = (x[1], -x[2], -x[3], -x[4])
trd(x) = 2 * x[1]
const I4 = (R(0), R(1), R(0), R(0))
const Z4 = (R(0), R(0), R(0), R(0))
kmul(x, y, d) = (x[1]*y[1] - d*x[2]*y[2], x[1]*y[2] + x[2]*y[1])
kinv(x, d) = (n = x[1]^2 + d*x[2]^2; (x[1]/n, -x[2]/n))
isnormQ(x::R, d) = (s = sqfree(numerator(x) * denominator(x));
                    all(hilbert(s, -d, p) == 1 for p in vcat(relevant_primes([s, d]), [0])))

function kdet(G, d)
    n = length(G); M = [copy(r) for r in G]; det = (R(1), R(0))
    for c in 1:n
        piv = findfirst(r -> M[r][c] != (0, 0), c:n); piv === nothing && return (R(0), R(0))
        piv += c - 1
        if piv != c; M[c], M[piv] = M[piv], M[c]; det = (-det[1], -det[2]); end
        det = kmul(det, M[c][c], d); inv = kinv(M[c][c], d)
        for r in c+1:n
            f = kmul(M[r][c], inv, d)
            M[r] = [(M[r][k][1] - kmul(f, M[c][k], d)[1], M[r][k][2] - kmul(f, M[c][k], d)[2]) for k in 1:n]
        end
    end
    return det
end

function trial(rng, d, be, m)
    rq() = Tuple(R(rand(rng, -2:2)) for _ in 1:4)
    nu = Matrix{NTuple{4,R}}(undef, m, m)
    for a in 1:m
        nu[a, a] = (R(rand(rng, [1, 2, 3, -1, -2, 5])), R(0), R(0), R(0))
        for b in a+1:m; z = rq(); nu[a, b] = z; nu[b, a] = qconj(z); end
    end
    E(x, y) = sum(trd(qmul(qmul(qmul(x[a], nu[a, b], d, be), qconj(y[b]), d, be), I4, d, be)) for a in 1:m, b in 1:m)
    lmul(q, x) = [qmul(q, xa, d, be) for xa in x]
    basisQ = [[a2 == a ? Tuple(R(k2 == k) for k2 in 1:4) : Z4 for a2 in 1:m] for a in 1:m for k in 1:4]
    tau(q) = qmul(qmul((R(0), R(-1, d), R(0), R(0)), qconj(q), d, be), I4, d, be)
    ok = all(E(u, u) == 0 for u in basisQ) && all(E(u, w) == -E(w, u) for u in basisQ, w in basisQ)
    bq = rq()
    ok &= all(E(lmul(bq, u), w) == E(u, lmul(tau(bq), w)) for u in basisQ, w in basisQ)
    Kb = [[a2 == a ? q : Z4 for a2 in 1:m] for a in 1:m for q in [(R(1), R(0), R(0), R(0)), (R(0), R(0), R(1), R(0))]]
    H(x, y) = (E(lmul(I4, x), y), E(x, y))
    n = 2m
    G = [[H(Kb[r], Kb[s]) for s in 1:n] for r in 1:n]
    ok &= all(G[s][r] == (G[r][s][1], -G[r][s][2]) for r in 1:n, s in 1:n)
    dt = kdet(G, d)
    ok &= dt[2] == 0 && dt[1] != 0
    ok &= isnormQ(dt[1] / R((-be)^m), d)
    # signature: the trace form 2 Re H on the Q-basis {e, i e : e in Kb} has signature (2m, 2m)
    QB = vcat(Kb, [lmul(I4, v) for v in Kb])
    S = [E(lmul(I4, x), y) for x in QB, y in QB]
    dg = diagonalize(S)
    ok &= (count(>(0), dg), count(<(0), dg)) == (2m, 2m)
    return ok
end

function main()
    C = Checks("qm_disc.jl")
    rng = MersenneTwister(7)
    for (d, be) in [(1, 3), (2, 5), (3, 2), (5, 2), (7, 3), (1, 7), (3, 5)], m in 1:3
        ok = all(trial(rng, d, be, m) for _ in 1:2)
        check(C, "B = (-$d, $be), m = $m: E alternating and tau-compatible, H hermitian of signature ($m,$m), det_K H = (-beta)^m mod norms (2 random nu)", ok)
    end
    finish(C)
end
main()
