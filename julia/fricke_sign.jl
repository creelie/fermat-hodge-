# fricke_sign.jl -- port of code/fricke_sign.py (32 checks).
# The sign of the Fricke self-isogeny by Velu's formulas.
#
# For N in {5, 7} let E_t: y^2 = x^3 + A(t) x + B(t), A = -27 c_4, B = -54 c_6,
# be the Fricke universal curve over X_0(N), w(t) = N^k/t (k = 3 for N = 5,
# k = 2 for N = 7), and C_t the rational cyclic subgroup of order N.  Exactly,
# with polynomials over Z in t and x stored as dictionaries:
#  (A) the division polynomial psi_N of E_t and the kernel polynomial of C_t,
#      its factor of degree (N-1)/2 in x;
#  (B) Velu's curve E' = E_t / C_t and j(E') = j(E_{w(t)});
#  (C) lambda(t)^2 = -t^2/25 (N = 5), -t^2/7 (N = 7), lambda(t) lambda(w(t)) = -N;
#  (D) the twist bookkeeping: Lambda^2 = -N on the pair twists, +N on the
#      fixed-point twist;
#  (E) the identity N^(k-1) B' A~ + A' B~ = 0, A~ = t^4 A(N^k/t), B~ = t^6 B(N^k/t);
#  (F) the analytic model f_tau(z) = z/tau.
# Difference from the Python program: sympy factors psi_N over Q(t).  Here the
# kernel polynomial is taken from the coefficients k_i recorded in
# lean/HodgeClosure.lean (kerE1_5, ..., kerE3_7) and certified: it divides
# psi_N exactly, and it and the cofactor psi_N / (N * kernel) are irreducible
# (each is irreducible modulo a prime after a specialisation of t), so that it
# is the only irreducible factor of degree (N-1)/2.  The rational-function
# identities of sympy are checked as polynomial identities after clearing
# denominators; each such reduction is stated next to the check.
# Run: julia --startup-file=no fricke_sign.jl

const NPASS = Ref(0); const NFAIL = Ref(0)
function check(name, ok)
    ok ? (NPASS[] += 1) : (NFAIL[] += 1)
    println(ok ? "PASS " : "FAIL ", name)
end

# ------------------------------------------------------------ Z[t]: coefficient vectors, constant term first
const ZP = Vector{BigInt}
zp(c...) = trim(BigInt[c...])
trim(a::ZP) = (while !isempty(a) && a[end] == 0; pop!(a); end; a)
deg(a::ZP) = length(a) - 1
function padd(a::ZP, b::ZP)
    r = zeros(BigInt, max(length(a), length(b)))
    r[1:length(a)] .+= a; r[1:length(b)] .+= b; trim(r)
end
pscal(c, a::ZP) = trim(BigInt(c) .* a)
psub(a::ZP, b::ZP) = padd(a, pscal(-1, b))
function pmul(a::ZP, b::ZP)
    (isempty(a) || isempty(b)) && return BigInt[]
    r = zeros(BigInt, length(a) + length(b) - 1)
    for (i, x) in enumerate(a), (j, y) in enumerate(b)
        r[i+j-1] += x * y
    end
    trim(r)
end
ppow(a::ZP, k) = k == 0 ? zp(1) : pmul(a, ppow(a, k - 1))
"t^d P(c/t) for deg P <= d"
ptilde(a::ZP, d, c) = trim(BigInt[(d - i <= deg(a) ? a[d-i+1] * BigInt(c)^(d - i) : BigInt(0)) for i in 0:d])
peval(a::ZP, t) = foldr((c, acc) -> acc * t + c, a; init=BigInt(0))

# ------------------------------------------------------------ Z[t][x]: (deg_x, deg_t) => coefficient
const BP = Dict{NTuple{2,Int},BigInt}
clean!(r::BP) = filter!(p -> p.second != 0, r)
function badd(a::BP, b::BP, s=1)
    r = copy(a)
    for (e, c) in b
        r[e] = get(r, e, BigInt(0)) + s * c
    end
    clean!(r)
end
function bmul(a::BP, b::BP)
    r = BP()
    for (e, c) in a, (f, d) in b
        k = e .+ f
        r[k] = get(r, k, BigInt(0)) + c * d
    end
    clean!(r)
end
bpow(a::BP, k) = k == 0 ? BP((0, 0) => BigInt(1)) : bmul(a, bpow(a, k - 1))
bscal(c, a::BP) = clean!(BP(e => c * v for (e, v) in a))
"the polynomial sum_i c_i(t) x^i with the given coefficients in Z[t] (c[1] = constant term)"
function bp(cs::Vector{ZP})
    r = BP()
    for (i, c) in enumerate(cs), (j, v) in enumerate(c)
        v != 0 && (r[(i - 1, j - 1)] = v)
    end
    r
end
xdeg(a::BP) = maximum(e[1] for e in keys(a))
"coefficient of x^i, in Z[t]"
function xcoeff(a::BP, i)
    c = BigInt[]
    for (e, v) in a
        e[1] == i || continue
        length(c) < e[2] + 1 && append!(c, zeros(BigInt, e[2] + 1 - length(c)))
        c[e[2]+1] = v
    end
    trim(c)
end
"division by a polynomial monic in x: (quotient, remainder)"
function bdivrem(a::BP, b::BP)
    n = xdeg(b); r = copy(a); q = BP()
    while !isempty(r) && xdeg(r) >= n
        d = xdeg(r); lead = BP((d - n, e[2]) => v for (e, v) in r if e[1] == d)
        q = badd(q, lead); r = badd(r, bmul(lead, b), -1)
    end
    q, r
end

"f_n with psi_n = f_n (n odd), psi_n = 2y f_n (n even), for y^2 = x^3 + A x + B"
function division_polynomial(A::ZP, B::ZP, N)
    X(k) = bp(vcat([BigInt[] for _ in 1:k], [zp(1)]))
    cst(c::ZP) = bp([c])
    y2 = badd(badd(X(3), bmul(cst(A), X(1))), cst(B))
    f = Dict{Int,BP}(0 => BP(), 1 => cst(zp(1)), 2 => cst(zp(1)),
        3 => bp([pscal(-1, pmul(A, A)), pscal(12, B), pscal(6, A), BigInt[], zp(3)]),
        4 => bscal(2, bp([psub(pscal(-8, pmul(B, B)), ppow(A, 3)), pscal(-4, pmul(A, B)), pscal(-5, pmul(A, A)),
                          pscal(20, B), pscal(5, A), BigInt[], zp(1)])))
    y16 = bpow(bscal(4, y2), 2)
    function F(n)
        haskey(f, n) && return f[n]
        m = n ÷ 2
        r = if n % 2 == 1
            if m % 2 == 0
                badd(bmul(bmul(F(m + 2), bpow(F(m), 3)), y16), bmul(F(m - 1), bpow(F(m + 1), 3)), -1)
            else
                badd(bmul(F(m + 2), bpow(F(m), 3)), bmul(bmul(F(m - 1), bpow(F(m + 1), 3)), y16), -1)
            end
        else
            bmul(F(m), badd(bmul(F(m + 2), bpow(F(m - 1), 2)), bmul(F(m - 2), bpow(F(m + 1), 2)), -1))
        end
        f[n] = r
    end
    F(N)
end

# ------------------------------------------------------------ F_p[x]
ptrim(a) = (while !isempty(a) && a[end] == 0; pop!(a); end; a)
function prem(a::Vector{Int}, b::Vector{Int}, p)
    r = copy(a); ib = invmod(b[end], p)
    while length(r) >= length(b)
        c = mod(r[end] * ib, p); k = length(r) - length(b)
        for (j, y) in enumerate(b)
            r[k+j] = mod(r[k+j] - c * y, p)
        end
        ptrim(r)
    end
    r
end
function pmulmod(a, b, f, p)
    r = zeros(Int, length(a) + length(b) - 1)
    for (i, x) in enumerate(a), (j, y) in enumerate(b)
        r[i+j-1] = mod(r[i+j-1] + x * y, p)
    end
    prem(ptrim(r), f, p)
end
function pgcdmod(a, b, p)
    while !isempty(b)
        a, b = b, prem(a, b, p)
    end
    a
end
"is f irreducible modulo p: gcd(f, x^(p^k) - x) = 1 for all k <= deg(f)/2"
function irreducible_mod(f::Vector{Int}, p)
    n = length(f) - 1; xq = [0, 1]
    for k in 1:n÷2
        y = [1]
        for _ in 1:p
            y = pmulmod(y, xq, f, p)
        end
        xq = y
        diff = vcat(xq, zeros(Int, max(0, 2 - length(xq)))); diff[2] = mod(diff[2] - 1, p); ptrim(diff)
        isempty(diff) && return false
        length(pgcdmod(f, diff, p)) > 1 && return false
    end
    true
end
const PRIMES = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
"first (p, t0) for which the specialisation t = t0 of g is irreducible modulo p, of the same degree in x; nothing if none"
function irreducibility_certificate(g::BP)
    n = xdeg(g)
    for p in PRIMES, t0 in 1:p-1
        gs = ptrim(Int[mod(peval(xcoeff(g, i), t0), p) for i in 0:n])
        length(gs) == n + 1 || continue
        irreducible_mod(gs, p) && return (p, t0)
    end
    nothing
end

# ------------------------------------------------------------ Laurent monomials c t^k
struct Mono
    c::Rational{BigInt}
    k::Int
end
Base.:*(a::Mono, b::Mono) = Mono(a.c * b.c, a.k + b.k)
Base.:(==)(a::Mono, b::Mono) = a.c == b.c && (a.k == b.k || a.c == 0)
subw(a::Mono, Nk) = Mono(a.c * (Nk // 1)^a.k, -a.k)          # t -> Nk/t
cst(c) = Mono(Rational{BigInt}(c), 0)

# polynomials in two further variables, exponents (i, j) => coefficient
const MP = Dict{NTuple{2,Int},BigInt}
mp(ps...) = MP(e => BigInt(c) for (e, c) in ps)

const DATA = Dict(
    7 => (c4=pmul(zp(49, 13, 1), zp(1, 5, 1)), c6=pmul(zp(49, 13, 1), zp(-7, 70, 63, 14, 1)), Nk=49, c=7,
          ker=[zp(1165563, 1338525, 586602, 132273, 16362, 1053, 27), zp(43659, 28782, 6777, 702, 27), zp(441, 117, 9), zp(1)]),
    5 => (c4=pmul(zp(5, 10, 1), zp(125, 22, 1)), c6=pmul(zp(-1, 4, 1), ppow(zp(125, 22, 1), 2)), Nk=125, c=25,
          ker=[zp(100125, 42372, 6282, 396, 9), zp(750, 132, 6), zp(1)]))

for N in (5, 7)
    d = DATA[N]; Nk = d.Nk; c = d.c
    A = pscal(-27, d.c4); B = pscal(-54, d.c6)
    m = (N - 1) ÷ 2
    # (A)
    psiN = division_polynomial(A, B, N)
    check("N=$N: psi_N has degree (N^2-1)/2 = $((N*N-1)÷2) in x", xdeg(psiN) == (N * N - 1) ÷ 2)
    ker = bp(d.ker)                               # x^m + k_1 x^(m-1) + ... + k_m
    cof, rem = bdivrem(psiN, ker)
    cert_k = irreducibility_certificate(ker); cert_c = irreducibility_certificate(cof)
    println("      kernel polynomial: ", join(["(" * join(["$(v) t^$(j-1)" for (j, v) in enumerate(xcoeff(ker, i)) if v != 0], " + ") * ") x^$i" for i in m:-1:0], " + "))
    println("      psi_N = kernel * cofactor, cofactor of degree $(xdeg(cof)) in x with leading coefficient $(xcoeff(cof, xdeg(cof))[1]);",
            " kernel irreducible modulo (p, t - t0) = $cert_k, cofactor irreducible modulo (p, t - t0) = $cert_c")
    check("N=$N: psi_N has exactly one irreducible factor of degree (N-1)/2 in x, the kernel polynomial, and it divides psi_N",
          isempty(rem) && xdeg(ker) == m && xcoeff(ker, m) == zp(1) && xdeg(cof) == (N * N - N) ÷ 2 && xcoeff(cof, xdeg(cof)) == zp(N) &&
          cert_k !== nothing && cert_c !== nothing && xdeg(cof) != m)
    # Newton: power sums S_1, S_2, S_3 of the roots
    coeffs = [d.ker[m+1-i] for i in 0:m]          # coeffs[i+1] = k_i
    e = vcat([zp(1)], [pscal((-1)^i, coeffs[i+1]) for i in 1:m])       # e[i+1] = e_i
    S = [zp(m)]
    for r in 1:3
        s = BigInt[]
        for i in 1:min(r - 1, m)
            s = padd(s, pscal((-1)^(i - 1), pmul(e[i+1], S[r-i+1])))
        end
        r <= m && (s = padd(s, pscal((-1)^(r - 1) * r, e[r+1])))
        push!(S, s)
    end
    S1, S2, S3 = S[2], S[3], S[4]
    tt = padd(pscal(6, S2), pscal(2m, A))                              # Velu: sum of t_Q over the kernel
    ww = padd(padd(pscal(10, S3), pscal(6, pmul(A, S1))), pscal(4m, B))  # Velu: sum of u_Q + x_Q t_Q
    A2 = psub(A, pscal(5, tt)); B2 = psub(B, pscal(7, ww))
    # A(w(t)) = At / t^4, B(w(t)) = Bt / t^6 with the polynomials At = t^4 A(N^k/t), Bt = t^6 B(N^k/t)
    At = ptilde(A, 4, Nk); Bt = ptilde(B, 6, Nk)
    disc(a, b) = padd(pscal(4, ppow(a, 3)), pscal(27, pmul(b, b)))
    # (B) j = 1728 * 4 a^3 / (4 a^3 + 27 b^2); j(a, b) = j(a', b') iff a^3 b'^2 = a'^3 b^2 (nonzero discriminants);
    #     j(E_w(t)) is computed from (At, Bt), the powers of t cancelling
    check("N=$N: Velu's curve has j(E') = j(E_w(t))",
          pmul(ppow(A2, 3), pmul(Bt, Bt)) == pmul(ppow(At, 3), pmul(B2, B2)) && !isempty(disc(A2, B2)) && !isempty(disc(At, Bt)))
    check("N=$N: j(E') is not j(E_t) (the isogeny is not an endomorphism)",
          pmul(ppow(A2, 3), pmul(B, B)) != pmul(ppow(A, 3), pmul(B2, B2)) && !isempty(disc(A, B)))
    # (C) lambda^2 = B' A(w) / (A' B(w)) = t^2 B' At / (A' Bt); it equals -t^2/c iff c B' At + A' Bt = 0
    lam2 = Mono(-1 // c, 2)
    check("N=$N: lambda(t)^2 = -t^2/$c", isempty(padd(pscal(c, pmul(B2, At)), pmul(A2, Bt))) && !isempty(A2) && !isempty(Bt))
    # lambda^4 = A'/A(w) = t^4 A'/At iff At = c^2 A';  lambda^6 = B'/B(w) = t^6 B'/Bt iff Bt = -c^3 B'
    check("N=$N: lambda^4 = A'/A(w) and lambda^6 = B'/B(w) are consistent", At == pscal(c^2, A2) && Bt == pscal(-c^3, B2))
    check("N=$N: lambda(t)^2 lambda(w(t))^2 = N^2", lam2 * subw(lam2, Nk) == cst(N * N))
    # lambda = i c' t up to sign with c'^2 = 1/c: lambda(t) lambda(w(t)) = i^2 c'^2 t (N^k/t) = -N^k/c
    check("N=$N: lambda(t) lambda(w(t)) = -N exactly (both signs of lambda give the same product)",
          cst(-1) * Mono(1 // c, 1) * subw(Mono(1 // 1, 1), Nk) == cst(-N))
    # (D) twists; variables (t, p): p u(t) = (t - p)(p t - N^k), p t^2 u(N^k/t) = (N^k - p t)(p N^k - N^k t)
    mmul(a, b) = (r = MP(); for (x, u) in a, (y, v) in b; r[x.+y] = get(r, x .+ y, BigInt(0)) + u * v; end; filter!(q -> q.second != 0, r))
    pu = mmul(mp((1, 0) => 1, (0, 1) => -1), mp((1, 1) => 1, (0, 0) => -Nk))
    pt2uw = mmul(mp((0, 0) => Nk, (1, 1) => -1), mp((0, 1) => Nk, (1, 0) => -Nk))
    check("N=$N: u_p(w(t)) = (N^k / t^2) u_p(t) for the pair twist", pt2uw == mmul(mp((0, 0) => Nk), pu))
    # t^2 u(N^k/t) = N^2k - N^k t^2 = -N^k (t^2 - N^k)
    check("N=$N: u(w(t)) = -(N^k / t^2) u(t) for the fixed-point twist t^2 - N^k", zp(BigInt(Nk)^2, 0, -Nk) == pscal(-Nk, zp(-Nk, 0, 1)))
    wprime = Mono(-Nk // 1, -2)                     # d/dt (N^k/t)
    check("N=$N: Lambda^2 = w'(t)^2 c(t)^2 lambda(t)^2 = -N on the pair twists", wprime * wprime * Mono(1 // Nk, 2) * lam2 == cst(-N))
    check("N=$N: Lambda^2 = +N on the fixed-point twist", wprime * wprime * Mono(-1 // Nk, 2) * lam2 == cst(N))
    # (E)
    check("N=$N: A~ = t^4 A(N^k/t) and B~ = t^6 B(N^k/t) are polynomials", deg(A) <= 4 && deg(B) <= 6 &&
          all(peval(At, t0) == t0^4 * (Rational{BigInt}(0) + sum(A[i+1] * (Nk // t0)^i for i in 0:deg(A))) &&
              peval(Bt, t0) == t0^6 * (Rational{BigInt}(0) + sum(B[i+1] * (Nk // t0)^i for i in 0:deg(B))) for t0 in BigInt.(1:8)))
    check("N=$N: $c B'(t) A~(t) + A'(t) B~(t) = 0 as polynomials", isempty(padd(pscal(c, pmul(B2, At)), pmul(A2, Bt))))
    L(a) = "[" * join(a, ", ") * "]"
    println("      Lean data: A = ", L(A))
    println("      Lean data: B = ", L(B))
    println("      Lean data: kernel k_i = ", join(L.(coeffs[2:end]), ", "))
    println("      Lean data: A' = ", L(A2), "  B' = ", L(B2))
    println("      Lean data: A~ = ", L(At), "  B~ = ", L(Bt))
end

# (F) the analytic model: f_tau(z) = z/tau, w(tau) = -1/(N tau); monomials in tau
for N in (5, 7)
    tau = Mono(1 // 1, 1); wtau = Mono(-1 // N, -1)
    inv(a::Mono) = Mono(1 / a.c, -a.k)
    # f_w(tau)(f_tau(z)) = z / (tau w(tau))
    check("N=$N: f_w(tau) o f_tau (z) = z / (tau w(tau)) = -N z", inv(tau * wtau) == cst(-N))
    # z/tau in Z + Z w(tau) iff z = tau (a + b w(tau)) = a tau - b/N
    check("N=$N: the kernel of f_tau is generated by 1/N modulo Z tau + Z", tau * cst(1) == Mono(1 // 1, 1) && tau * wtau == cst(-1 // N))
end

println("fricke_sign.jl: $(NPASS[]) checks passed, $(NFAIL[]) failed")
NFAIL[] > 0 && exit(1)
