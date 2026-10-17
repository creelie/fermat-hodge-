# eigencharacter.jl -- the eigencharacter of the polarisation (Sect. VII of
# the paper, Lean Section 2), in exact integer arithmetic.
# In Z[sqrt(-d)] with a hermitian form H of signature eps and the alternating
# form eta(x,y) = Tr(sqrt(-d) H(x,y)): eta(tau x, tau y) = N(tau) eta(x,y),
# N is multiplicative, N(2 + sqrt(-d)) != 1, and tau^(2n) != N(tau)^n.
# Run: julia eigencharacter.jl
struct Q; a::BigInt; b::BigInt; end           # a + b sqrt(-d)
qadd(x, y) = Q(x.a + y.a, x.b + y.b)
qmul(d, x, y) = Q(x.a * y.a - d * x.b * y.b, x.a * y.b + x.b * y.a)
qconj(x) = Q(x.a, -x.b)
qnorm(d, x) = x.a^2 + d * x.b^2
qscale(c, x) = Q(c * x.a, c * x.b)
trroot(d, z) = -2 * d * z.b                   # Tr(sqrt(-d) z)
function herm(d, eps, x, y)
    acc = Q(0, 0)
    for (e, xi, yi) in zip(eps, x, y)
        acc = qadd(acc, qscale(e, qmul(d, xi, qconj(yi))))
    end
    acc
end
eta(d, eps, x, y) = trroot(d, herm(d, eps, x, y))
vscale(d, t, x) = [qmul(d, t, xi) for xi in x]
qpow(d, t, k) = k == 0 ? Q(1, 0) : qmul(d, t, qpow(d, t, k - 1))

ds = [1, 2, 3, 5, 7, 11, 15, 19]
eps4 = [1, 1, -1, -1]
taus = [Q(2, 1), Q(1, 1), Q(3, -2), Q(0, 1), Q(5, 3), Q(7, -4), Q(-3, 5)]
vecs = [[Q(1,0), Q(0,1), Q(2,-1), Q(1,1)], [Q(0,2), Q(1,-1), Q(3,0), Q(-1,2)],
        [Q(1,1), Q(1,1), Q(1,1), Q(1,1)], [Q(-2,3), Q(0,0), Q(1,-4), Q(2,2)],
        [Q(5,-7), Q(2,9), Q(-6,1), Q(0,3)]]
ok = true; n_eigen = 0
for d in ds, t in taus, x in vecs, y in vecs
    global ok &= eta(d, eps4, vscale(d, t, x), vscale(d, t, y)) == qnorm(d, t) * eta(d, eps4, x, y)
    global n_eigen += 1
end
println("eta(tau x, tau y) = N(tau) eta(x, y): ", n_eigen, " instances, ", ok ? "all hold" : "FAIL")
ok2 = all(qnorm(d, qmul(d, t, s)) == qnorm(d, t) * qnorm(d, s) for d in ds, t in taus, s in taus)
println("N multiplicative on the sample: ", ok2)
ok3 = all(qnorm(d, Q(2, 1)) != 1 for d in ds)
println("N(2 + sqrt(-d)) != 1 for every d: ", ok3)
ok4 = all(qpow(d, Q(2, 1), 2n) != Q(qnorm(d, Q(2, 1))^n, 0) for d in ds, n in 1:8)
println("tau^(2n) != N(tau)^n at tau = 2 + sqrt(-d), n = 1..8: ", ok4)
# the ratio of the two characters is (tau / conj tau)^n, of norm one and not 1
ok5 = all(qnorm(d, qpow(d, t, 2n)) == qnorm(d, t)^(2n) for d in ds, t in taus, n in 1:4)
println("|tau^(2n)|^2 = N(tau)^(2n): ", ok5)
allok = ok && ok2 && ok3 && ok4 && ok5
println("eigencharacter.jl: ", allok ? "PASS" : "FAIL")
exit(allok ? 0 : 1)
