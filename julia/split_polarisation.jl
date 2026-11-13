# split_polarisation.jl -- Lemma lem:splitpol on four totally real sextic fields.
# L = Q[t]/(f), K = Q(sqrt(-d)), M = K L.  For a in L^x the hermitian form
# H_a(x,y) = Tr_{M/K}(a x ybar) on the K-space M has, in the K-basis
# 1, t, ..., t^5, the rational Gram matrix (Tr_{L/Q}(a t^(i+j))), so
# det H_a = disc(f) N_{L/Q}(a).  H_a has signature (3,3) iff a is negative at
# exactly three real places, and is then split iff -det H_a is a norm from K,
# iff (-det H_a, -d)_p = 1 at every prime p.  For each of the twenty sign
# patterns we find a with H_a split and recheck the Gram determinant, the
# signature (exact diagonalisation) and the symbols; non-split classes occur
# as well.  Exact integer arithmetic except the signs of g at the roots, which
# are computed in Float64 for elements bounded away from zero.
# Run: julia --startup-file=no split_polarisation.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms
using LinearAlgebra

function companion(f)                 # f monic, coefficients low -> high
    n = length(f) - 1
    Cm = zeros(BigInt, n, n)
    for i in 2:n; Cm[i, i-1] = 1; end
    for i in 1:n; Cm[i, n] = -f[i]; end
    return Cm
end
detQ(M) = det(Rational{BigInt}.(M))

# ---- Sturm count of real roots ----
function pdivrem(a, b)
    a = copy(a)
    while length(a) >= length(b) && any(!iszero, a)
        q = a[end] / b[end]; s = length(a) - length(b)
        for (i, c) in enumerate(b); a[i+s] -= q * c; end
        pop!(a)
    end
    while !isempty(a) && a[end] == 0; pop!(a); end
    return a
end
function sturm_count(f)
    p0 = Rational{BigInt}.(f); p1 = [Rational{BigInt}(i * f[i+1]) for i in 1:length(f)-1]
    chain = [p0, p1]
    while true
        r = pdivrem(chain[end-1], chain[end])
        isempty(r) && break
        push!(chain, -r)
    end
    lead(p) = sign(p[end]); minus(p) = sign(p[end]) * (-1)^(length(p) - 1)
    var(s) = (s = filter(!iszero, s); count(i -> s[i] != s[i+1], 1:length(s)-1))
    return var(minus.(chain)) - var(lead.(chain))
end

# ---- distinct-degree factorisation mod p ----
function ddf_degrees(f, p)
    trim(a) = (a = [mod(x, p) for x in a]; while !isempty(a) && a[end] == 0; pop!(a); end; a)
    function pmod(a, b)
        a = trim(a); b = trim(b); iv = invmod(b[end], p)
        while length(a) >= length(b)
            q = mod(a[end] * iv, p); s = length(a) - length(b)
            for (i, c) in enumerate(b); a[i+s] = mod(a[i+s] - q * c, p); end
            a = trim(a)
        end
        return a
    end
    function pmul(a, b, m)
        r = zeros(Int, length(a) + length(b) - 1)
        for (i, x) in enumerate(a), (j, y) in enumerate(b); r[i+j-1] = mod(r[i+j-1] + x * y, p); end
        return pmod(r, m)
    end
    function pgcd(a, b)
        a = trim(a); b = trim(b)
        while !isempty(b); a, b = b, pmod(a, b); end
        iv = invmod(a[end], p); return [mod(x * iv, p) for x in a]
    end
    function pdivexact(a, b)
        a = [mod(x, p) for x in a]; q = zeros(Int, length(a) - length(b) + 1); iv = invmod(b[end], p)
        for s in length(a)-length(b):-1:0
            c = mod(a[s+length(b)] * iv, p); q[s+1] = c
            for (i, y) in enumerate(b); a[i+s] = mod(a[i+s] - c * y, p); end
        end
        return q
    end
    function ppow(base, e, m)
        r = [1]
        while e > 0
            isodd(e) && (r = pmul(r, base, m)); base = pmul(base, base, m); e >>= 1
        end
        return r
    end
    fp = trim(f); dfp = trim([i * f[i+1] for i in 1:length(f)-1])
    length(pgcd(fp, dfp)) != 1 && return nothing
    degs = Int[]; g = fp; h = [0, 1]; k = 0
    while length(g) - 1 > 0
        k += 1; h = ppow(h, p, g)
        df = copy(h); length(df) < 2 && append!(df, zeros(Int, 2 - length(df)))
        df[2] = mod(df[2] - 1, p); df = trim(df)
        if isempty(df); append!(degs, fill(k, div(length(g) - 1, k))); break; end
        c = pgcd(g, df)
        if length(c) > 1
            append!(degs, fill(k, div(length(c) - 1, k))); g = pdivexact(g, c)
            length(g) > 1 && (h = pmod(h, g))
        end
    end
    return sort(degs)
end
isprime_(n) = n >= 2 && all(n % q != 0 for q in 2:isqrt(n))

const FACT = Dict{BigInt,Vector{Int}}()
function fastprimes(x)
    get!(FACT, BigInt(x)) do
        n = Int128(abs(x)); ps = Int[]; p = Int128(2)
        while p * p <= n
            if n % p == 0
                push!(ps, Int(p)); while n % p == 0; n = div(n, p); end
            end
            p += (p == 2 ? 1 : 2)
        end
        n > 1 && push!(ps, Int(n))
        ps
    end
end
function hs(x, d, cache)
    get!(cache, (x, d)) do
        ps = union(Set(fastprimes(x)), Set(primes_of(d)), Set([2]))
        xi = Int128(x)
        sort([p for p in ps if hilb(xi, Int128(-d), p) == -1])
    end
end
symd(a, b) = sort(symdiff(a, b))
"(a,b)_p for nonzero integers, from valuations and unit parts (no squarefree reduction needed)"
function hilb(a::Integer, b::Integer, p::Integer)
    al = 0; while a % p == 0; a = div(a, p); al += 1; end
    be = 0; while b % p == 0; b = div(b, p); be += 1; end
    if p == 2
        e(x) = mod(div(x - 1, 2), 2); w(x) = mod(div(x * x - 1, 8), 2)
        u = mod(a, 8); v = mod(b, 8)
        return isodd(e(u) * e(v) + al * w(v) + be * w(u)) ? -1 : 1
    end
    r = 1
    (isodd(al) && isodd(be) && p % 4 == 3) && (r = -r)
    isodd(be) && (r *= legendre(mod(a, p), p))
    isodd(al) && (r *= legendre(mod(b, p), p))
    return r
end

function analyse!(C, name, f, ds; galois = false)
    n = 6
    check(C, "$name: f = $f has six real roots (Sturm)", sturm_count(f) == 6)
    irr = [p for p in 3:199 if isprime_(p) && ddf_degrees(f, p) == [6]]
    check(C, "$name: f irreducible mod p = $(irr[1]) (hence over Q)", !isempty(irr))
    if galois
        pats = Dict{Vector{Int},Int}()
        for p in 3:399
            isprime_(p) || continue
            dg = ddf_degrees(f, p); dg === nothing || get!(pats, dg, p)
        end
        need = [[6], [1, 5], [1, 1, 1, 1, 2]]
        check(C, "$name: Frobenius cycle types (6), (1,5), (1,1,1,1,2) occur (at p = $([get(pats, k, 0) for k in need])): Galois group S_6",
              all(haskey(pats, k) for k in need))
    end
    Cm = companion(f); P = [Matrix{BigInt}(I, n, n)]
    for _ in 1:2n; push!(P, P[end] * Cm); end
    trm(M) = sum(M[i, i] for i in 1:n)
    disc = detQ([trm(P[i+j+1]) for i in 0:n-1, j in 0:n-1]); @assert denominator(disc) == 1
    disc = BigInt(disc)
    check(C, "$name: det H_1 = disc(f) = $disc > 0", disc > 0)
    roots = sort(real.(eigvals(Float64.(companion(f)))))
    elems = []
    box = vcat([vcat(collect(c), [0, 0]) for c in Iterators.product(-3:3, -3:3, -3:3, -3:3)][:],
               [collect(c) for c in Iterators.product(-1:1, -1:1, -1:1, -1:1, -1:1, -1:1)][:])
    fp = [k * f[k+1] for k in 1:6]; fp[findfirst(!iszero, fp)] < 0 && (fp = -fp)
    push!(box, fp)
    seen = Set{Vector{Int}}()
    for c in box
        all(iszero, c) && continue
        c[findfirst(!iszero, c)] < 0 && continue
        c in seen && continue; push!(seen, c)
        vals = [sum(c[k+1] * r^k for k in 0:5) for r in roots]
        minimum(abs.(vals)) < 1e-6 && continue
        A = sum(c[k+1] * P[k+1] for k in 0:5)
        N = detQ(A); @assert denominator(N) == 1 && N != 0
        N = BigInt(N); sv = [v < 0 for v in vals]
        push!(elems, (c, sv, N, A))
    end
    signok = all((e[3] < 0) == isodd(count(e[2])) for e in elems)
    check(C, "$name: $(length(elems)) small elements g; sign of N(g) = parity of negative places", signok)
    cache = Dict()
    pats = [Tuple(i in J for i in 1:6) for J in [collect(s) for s in Iterators.filter(s -> length(s) == 3, [findall(b -> b, digits(m, base = 2, pad = 6) .== 1) for m in 0:63])]]
    for d in ds
        table = Dict{Tuple{Vector{Bool},Vector{Int}},Any}()
        for (c, sv, N, A) in elems; get!(table, (sv, hs(N, d, cache)), (c, [N], A)); end
        cF, svF, NF, AF = elems[end]
        for (c, sv, N, A) in elems[1:end-1]
            get!(table, (sv .⊻ svF, symd(hs(N, d, cache), hs(NF, d, cache))), ((c, "f'"), [N, NF], A * AF))
        end
        target = hs(-disc, d, cache)
        found = Dict{Vector{Bool},Any}(); nonsplit = false
        for (c1, sv1, N1, A1) in elems
            h1 = hs(N1, d, cache)
            for pat in pats
                for want in (collect(pat), .!collect(pat))
                    key = (sv1 .⊻ want, symd(h1, target))
                    if haskey(table, key) && !haskey(found, collect(pat))
                        c2, N2, A2 = table[key]; found[collect(pat)] = (c1, c2, vcat([N1], N2), A1 * A2)
                    end
                end
            end
            count(sv1) == 3 && h1 != target && (nonsplit = true)
        end
        allok = length(found) == 20
        exact = allok
        for (pat, (c1, c2, Ns, A)) in found
            NN = prod(Ns)
            G = [trm(A * P[i+j+1]) for i in 0:n-1, j in 0:n-1]
            D = detQ(G)
            dg = diagonalize(G)
            neg = count(<(0), dg)
            facs = vcat([BigInt(-1), disc], Ns)          # -D = (-1) disc N(a), N(a) = prod Ns
            ps = union(Set(primes_of(d)), Set([2]), [Set(fastprimes(x)) for x in facs[2:end]]...)
            exact &= D == disc * NN && D < 0 && neg == 3 &&
                     all(prod(hilb(x, BigInt(-d), p) for x in facs) == 1 for p in ps)
        end
        check(C, "$name, K = Q(sqrt(-$d)): for all 20 sign patterns an a with H_a of signature (3,3) and -det H_a a norm from K; Gram determinant, signature and symbols rechecked exactly; non-split classes occur", exact && nonsplit)
    end
end

function main()
    C = Checks("split_polarisation.jl")
    function cyclo_plus(m)
        rs = [2cos(2pi * k / m) for k in 1:div(m, 2) if gcd(k, m) == 1]
        c = [1.0]
        for r in rs; c = [0.0; c] .- r .* [c; 0.0]; end      # coefficients low -> high
        return [round(Int, x) for x in c]
    end
    for m in (21, 28, 36)
        analyse!(C, "Q(zeta_$m)^+", cyclo_plus(m), [1, 3, 7, 2, 5])
    end
    analyse!(C, "S_6 field", [-1, 3, 8, -4, -9, -1, 1], [1, 3, 7, 2, 5]; galois = true)
    finish(C)
end
main()
