# fricke_picard.jl -- port of code/fricke_picard.py (12 checks).
# Point counts for the Picard number of the member X_1 of each Fricke family
# A_N (the twist of the Fricke universal curve at the pair {1, N^k}), N = 5, 7.
#
# For a prime l of good reduction and q = l^i the trace of Frob_q on the
# orthogonal complement T (rank 6) of the trivial lattice is
#     s_i = sum over t in P^1(F_q) of W_t - 1 - q^2 - 2q,
# W_t the number of F_q-points of the Weierstrass fibre over t.  The
# characteristic polynomial P of Frob_l on T follows from s_1, ..., s_m by
# Newton's identities and the functional equation x^6 P(l^2/x) = eps l^6 P(x).
# Expected: P = x^6 - 726 x^3 + 11^6 (N = 7, l = 11) and
# P = x^6 + 6x^5 + 56x^4 + 392x^3 + 2744x^2 + 14406x + 7^6 (N = 5, l = 7).
# The finite fields are handled by Zech logarithms.
# Difference from the Python program: sympy's factorisation over Q(sqrt(-N))
# is replaced by an exact search for the cubic g in Q(sqrt(-N))[x] with
# g gbar = P (coefficients in the half-integers a + b sqrt(-N)), and the
# irreducibility of g by its reduction modulo a split prime; P = g gbar with
# g irreducible over Q(sqrt(-N)) and g != gbar gives the irreducibility over Q.
# Run: julia --startup-file=no fricke_picard.jl

const NPASS = Ref(0); const NFAIL = Ref(0)
function check(name, ok)
    ok ? (NPASS[] += 1) : (NFAIL[] += 1)
    println(ok ? "PASS " : "FAIL ", name)
end

const DATA = Dict(
    7 => (c4=[[49, 13, 1], [1, 5, 1]], c6=[[49, 13, 1], [-7, 70, 63, 14, 1]], Nk=49),
    5 => (c4=[[5, 10, 1], [125, 22, 1]], c6=[[-1, 4, 1], [125, 22, 1], [125, 22, 1]], Nk=125))
function polymul(a, b)
    r = zeros(BigInt, length(a) + length(b) - 1)
    for (i, x) in enumerate(a), (j, y) in enumerate(b)
        r[i+j-1] += x * y
    end
    r
end

# F_{l^n} by Zech logarithms: elements are logs 0..q-2, and -1 stands for 0
struct GF
    l::Int
    n::Int
    q::Int
    zech::Vector{Int}
    cst::Vector{Int}          # logs of 1..l-1
end
function GF(l, n)
    q = l^n
    code(v) = foldr((d, acc) -> acc * l + d, v; init=0)
    for cc in Iterators.product(ntuple(_ -> 0:l-1, n)...)
        coeffs = reverse(collect(cc))             # x^n = c_{n-1} x^{n-1} + ... + c_0, lexicographic order
        coeffs[1] == 0 && continue
        v = zeros(Int, n); v[1] = 1
        logof = fill(-1, q); expo = Int[]; ok = true
        for k in 0:q-2
            key = code(v)
            if logof[key+1] >= 0
                ok = false; break
            end
            logof[key+1] = k; push!(expo, key)
            top = v[end]
            v = vcat(0, v[1:end-1])
            for i in 1:n
                v[i] = mod(v[i] + top * coeffs[i], l)
            end
        end
        (ok && code(v) == expo[1]) || continue
        digits_(key) = [(key ÷ l^(i - 1)) % l for i in 1:n]
        one = digits_(expo[1])
        zech = Vector{Int}(undef, q - 1)
        for k in 0:q-2
            s = mod.(one .+ digits_(expo[k+1]), l)
            zech[k+1] = all(==(0), s) ? -1 : logof[code(s)+1]
        end
        return GF(l, n, q, zech, [logof[c+1] for c in 1:l-1])
    end
    error("no primitive polynomial")
end
@inline function gadd(F::GF, a::Int, b::Int)
    a < 0 && return b
    b < 0 && return a
    z = F.zech[mod(b - a, F.q - 1)+1]
    z < 0 ? -1 : mod(a + z, F.q - 1)
end
@inline gmul(F::GF, a::Int, b::Int) = (a < 0 || b < 0) ? -1 : mod(a + b, F.q - 1)
cint(F::GF, c) = (r = Int(mod(c, F.l)); r == 0 ? -1 : F.cst[r])
function evalpoly_(F::GF, coeffs, tlog)
    r = -1
    for c in Iterators.reverse(coeffs)
        r = gadd(F, gmul(F, r, tlog), cint(F, c))
    end
    r
end
"q + 1 + sum_x chi(x^3 + a x + b), chi(g^k) = (-1)^k"
function weierstrass_count(F::GF, a::Int, b::Int)
    q1 = F.q - 1
    total = F.q + 1
    b >= 0 && (total += 1 - 2 * (b & 1))
    for k in 0:q1-1
        x3 = mod(3k, q1)
        ax = a < 0 ? -1 : mod(a + k, q1)
        v = gadd(F, gadd(F, x3, ax), b)
        v >= 0 && (total += 1 - 2 * (v & 1))
    end
    total
end
"s_i, i = 1..imax: traces of Frob_{l^i} on the complement of the trivial lattice"
function traces(N, l, imax, twist)
    d = DATA[N]
    c4 = BigInt[1]; for f in d.c4; c4 = polymul(c4, f); end
    c6 = BigInt[1]; for f in d.c6; c6 = polymul(c6, f); end
    A = -27 .* c4; B = -54 .* c6
    if twist
        u = polymul([-1, 1], [-d.Nk, 1])
        A = polymul(A, polymul(u, u)); B = polymul(B, polymul(u, polymul(u, u)))
    end
    out = Int[]
    for i in 1:imax
        F = GF(l, i); q = F.q
        total = weierstrass_count(F, cint(F, A[1]), cint(F, B[1]))             # t = 0
        for k in 0:q-2
            total += weierstrass_count(F, evalpoly_(F, A, k), evalpoly_(F, B, k))
        end
        total += weierstrass_count(F, cint(F, A[end]), cint(F, B[end]))        # t = infinity
        push!(out, total - 1 - q * q - 2q)
    end
    out
end

const QQ = Rational{BigInt}
"Newton's identities: e_0, ..., e_m from the power sums"
function elementary_from_traces(s)
    e = QQ[1]
    for k in 1:length(s)
        push!(e, sum((-1)^(i - 1) * e[k-i+1] * s[i] for i in 1:k) / k)
    end
    e
end
"coefficients c_j of P = sum c_j x^(dim-j): c_j = (-1)^j e_j (j <= m), c_(dim-j) = eps l^(2(dim/2-j)) c_j"
function complete_with_functional_equation(e, l, dim=6)
    m = length(e) - 1; results = []
    for eps in (1, -1)
        c = Vector{Union{Nothing,QQ}}(nothing, dim + 1)
        for j in 0:m
            c[j+1] = (-1)^j * e[j+1]
        end
        ok = true
        for j in 0:dim
            c[j+1] === nothing && continue
            k = dim - j
            val = eps * QQ(l)^(2 * (dim ÷ 2 - j)) * c[j+1]
            if c[k+1] === nothing
                c[k+1] = val
            elseif c[k+1] != val
                ok = false
            end
        end
        ok && all(!isnothing, c) && push!(results, (eps, QQ[v for v in c]))
    end
    results
end

# Q[x], constant term first
trim(a) = (while !isempty(a) && a[end] == 0; pop!(a); end; a)
function pdivrem(a::Vector{QQ}, b::Vector{QQ})
    r = copy(a); q = zeros(QQ, max(length(a) - length(b) + 1, 0))
    while length(r) >= length(b)
        c = r[end] / b[end]; k = length(r) - length(b)
        q[k+1] = c
        for (j, y) in enumerate(b)
            r[k+j] -= c * y
        end
        trim(r)
    end
    trim(q), r
end
function pgcd(a::Vector{QQ}, b::Vector{QQ})
    while !isempty(b)
        a, b = b, pdivrem(a, b)[2]
    end
    a
end
const CYCLO = Dict{Int,Vector{QQ}}()
function cyclotomic(n)
    get!(CYCLO, n) do
        f = vcat(QQ[-1], zeros(QQ, n - 1), QQ[1])
        for d in 1:n-1
            n % d == 0 && (f = pdivrem(f, cyclotomic(d))[1])
        end
        f
    end
end

"all cubics g = x^3 + a x^2 + b x + c over Q(sqrt(-N)), half-integral coefficients, with g gbar = P; entries (2a0, 2a1, 2b0, 2b1, 2c0, 2c1)"
function split_over_K(Pc::Vector{BigInt}, N, l)       # Pc[j+1] = coefficient of x^(6-j)
    p5, p4, p3, p2, p1, p0 = Pc[2], Pc[3], Pc[4], Pc[5], Pc[6], Pc[7]
    sols = NTuple{6,Int}[]
    A0 = Int(p5)                                       # a + abar = 2 a0 = p5
    cs = [(C0, C1) for C1 in -2l^3:2l^3 for C0 in -2l^3:2l^3 if C0^2 + N * C1^2 == 4 * p0]
    for A1 in -6l:6l, (C0, C1) in cs, B1 in -6l^2:6l^2
        # all quantities doubled: a = (A0 + A1 s)/2, s = sqrt(-N); norm(a) = (A0^2 + N A1^2)/4
        # x^4: a abar + b + bbar = p4  ->  B0 = p4 - (A0^2 + N A1^2)/4
        (A0^2 + N * A1^2) % 4 == 0 || continue
        B0 = Int(p4) - (A0^2 + N * A1^2) ÷ 4
        # x^3: a bbar + abar b + c + cbar = (A0 B0 + N A1 B1)/2 + C0 = p3
        A0 * B0 + N * A1 * B1 + 2 * C0 == 2 * p3 || continue
        # x^2: a cbar + abar c + b bbar = (A0 C0 + N A1 C1)/2 + (B0^2 + N B1^2)/4 = p2
        2 * (A0 * C0 + N * A1 * C1) + B0^2 + N * B1^2 == 4 * p2 || continue
        # x^1: b cbar + bbar c = (B0 C0 + N B1 C1)/2 = p1
        B0 * C0 + N * B1 * C1 == 2 * p1 || continue
        push!(sols, (A0, A1, B0, B1, C0, C1))
    end
    sols
end
"is the cubic with doubled coefficients sol irreducible modulo a prime above p, sqrt(-N) -> s"
function cubic_irreducible_mod(sol, p, s)
    i2 = invmod(2, p)
    a = mod((sol[1] + sol[2] * s) * i2, p); b = mod((sol[3] + sol[4] * s) * i2, p); c = mod((sol[5] + sol[6] * s) * i2, p)
    !any(mod(x^3 + a * x^2 + b * x + c, p) == 0 for x in 0:p-1)
end
rs(x) = denominator(x) == 1 ? string(numerator(x)) : "$(numerator(x))/$(denominator(x))"
fmt(P) = join([(c < 0 ? "- " : (j == 1 ? "" : "+ ")) * (abs(c) == 1 && j < 7 ? "" : string(abs(c))) * (j < 6 ? "x^$(7-j)" : j == 6 ? "x" : "")
               for (j, c) in enumerate(P) if c != 0], " ")

const EXPECTED = Dict((7, 11) => BigInt[1, 0, 0, -726, 0, 0, BigInt(11)^6],
                      (5, 7) => BigInt[1, 6, 56, 392, 2744, 14406, BigInt(7)^6])
function report(N, l, imax)
    println("-- N = $N, l = $l, traces of Frob_{l^i} on T for i <= $imax")
    s = traces(N, l, imax, true)
    println("      s_i = ", s)
    e = elementary_from_traces(s)
    cands = complete_with_functional_equation(e, l)
    check("N=$N, l=$l: the traces determine the sign of the functional equation (the middle coefficient is nonzero)",
          length(cands) == 1 && e[4] != 0)
    eps, c = cands[1]
    integral = all(denominator(v) == 1 for v in c)
    Pc = BigInt[numerator(v) for v in c]
    println("      P(x) = ", fmt(Pc))
    check("N=$N, l=$l: eps = +1 and P has integer coefficients; P = " * fmt(EXPECTED[(N, l)]),
          eps == 1 && integral && Pc == EXPECTED[(N, l)])
    Q = QQ[c[7-k] * QQ(l)^k / QQ(l)^6 for k in 0:6]                  # P(l x)/l^6, constant term first
    println("      P(l x)/l^6 = ", join(["($(rs(Q[k+1]))) x^$k" for k in 6:-1:0 if Q[k+1] != 0], " + "))
    cyclo = [n for n in 1:30 if length(pgcd(Q, cyclotomic(n))) > 1]
    check("N=$N, l=$l: no root of P is l times a root of unity (cyclotomic factors of P(l x): $(isempty(cyclo) ? "none" : string(cyclo))), so rho(X_1) = 16", isempty(cyclo))
    sols = split_over_K(Pc, N, l)
    conj_(g) = (g[1], -g[2], g[3], -g[4], g[5], -g[6])
    h(v, w) = "(" * rs(v // 2) * " + " * rs(w // 2) * " sqrt(-$N))"
    ok = length(sols) == 2 && sols[2] == conj_(sols[1]) && sols[1] != sols[2]
    cert = nothing
    if ok
        g = sols[2]
        println("      over Q(sqrt(-$N)): P = g gbar, g = x^3 + $(h(g[1], g[2])) x^2 + $(h(g[3], g[4])) x + $(h(g[5], g[6]))")
        for p in (3, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97), s_ in 1:p-1
            (p == l || p == N || mod(s_^2 + N, p) != 0) && continue
            if cubic_irreducible_mod(g, p, s_)
                cert = (p, s_); break
            end
        end
        println("      g is irreducible modulo the prime above p with sqrt(-$N) -> s, (p, s) = $cert")
    end
    check("N=$N, l=$l: P(l x)/l^6 is irreducible over Q and splits as g gbar, deg g = 3, over Q(sqrt(-$N)) (Frobenius commutes with f^*)",
          ok && cert !== nothing)
end
function inert(N, l, imax)
    s = traces(N, l, imax, true)
    println("-- N = $N, l = $l inert in Q(sqrt(-$N)): s_i = $s")
    check("N=$N, l=$l: Frobenius exchanges the two eigenspaces of f^*, so the odd traces vanish",
          powermod(mod(-N, l), (l - 1) ÷ 2, l) == l - 1 && all(s[i] == 0 for i in 1:2:imax))
end

# control: the rational surfaces R_N, complement of the trivial lattice = Mordell-Weil part of rank 2
for (N, l) in ((7, 5), (5, 7))
    s = traces(N, l, 2, false)
    check("control R_$N, l=$l: the traces $s on the Mordell-Weil part are q times the trace of a permutation of two generators",
          all(abs(si) <= 2 * l^i && mod(si, l^i) == 0 for (i, si) in enumerate(s)))
end
# split primes: -7 = 4^2 mod 11, -5 = 3^2 mod 7
report(7, 11, 3)
report(5, 7, 4)
# inert primes: -7 is not a square mod 5, -5 is not a square mod 11
inert(7, 5, 3)
inert(5, 11, 3)

println("fricke_picard.jl: $(NPASS[]) checks passed, $(NFAIL[]) failed")
NFAIL[] > 0 && exit(1)
