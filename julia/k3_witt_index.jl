# k3_witt_index.jl -- the finite computations behind Lemma lem:witt, Theorem
# Corollaries cor:rho17, cor:rho16 and Theorem thm:rmcrit with Corollaries
# cor:rmcovered, cor:rmopen: rational quadratic spaces T of signature (2, r-2)
# and their embeddings in U^3 + <-m>, the Witt index criterion in rank six,
# and the local criterion for trace forms T = Tr_{E/Q} W of ternary forms W
# over a real quadratic field E = Q(sqrt e).
# The local symbols over E_P are computed independently of the trace form:
# by Hensel lifting at primes split in E, by the tame symbol at odd primes
# inert or ramified in E.  Exact integer arithmetic; fixed seeds.
# Run: julia --startup-file=no k3_witt_index.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms
using Random

const U = [1, -1]
const U3 = vcat(U, U, U)

"rank 6, signature (2,4): Witt index 2 iff T_p ~ U^3 at every p with -d(T) a square in Q_p"
function witt2_rank6(T)
    d = disc(T)
    ps = [p for p in relevant_primes(T) if is_square_Qp(-d, p)]
    return all(hasse(T, p) == hasse(U3, p) for p in ps)
end

issqf(n) = all(n % (q * q) != 0 for q in 2:isqrt(n))
const SQF = [l for l in 1:2999 if issqf(l)]

"smallest squarefree lam < 3000 with T ~ lam (U^2 + <-1,-d>); returns (lam, m) with T + <lam> ~ U^3 + <-m>"
function find_lam_m(T)
    d = disc(T)
    for lam in SQF
        if isometric(T, scale(vcat(U, U, [-1, -d]), lam))
            m = sqfree(lam * d)
            (isometric(vcat(T, [lam]), vcat(U3, [-m])) && embeds(T, vcat(U3, [-m]))) || return nothing
            return lam, m
        end
    end
    return nothing
end

function some_m(T, ps)
    ps = sort(collect(ps))
    for mask in 0:(1 << length(ps)) - 1
        m = 1
        for (i, p) in enumerate(ps); (mask >> (i - 1)) & 1 == 1 && (m *= p); end
        embeds(T, vcat(U3, [-m])) && return m
    end
    return nothing
end

# ---- arithmetic in E = Q(sqrt e): pairs (u, v) = u + v sqrt e ----------------
Nm(a, e) = a[1]^2 - e * a[2]^2
mulE(a, b, e) = (a[1] * b[1] + e * a[2] * b[2], a[1] * b[2] + a[2] * b[1])
negE(a) = (-a[1], -a[2])
"diagonal form of Tr_{E/Q}<a>: Gram [[2u, 2ve], [2ve, 2ue]], determinant 4 e N(a)"
tr_binary(a, e) = a[1] == 0 ? [1, -1] : [2 * a[1], 2 * a[1] * e * Nm(a, e)]
trace_form(W, e) = vcat([tr_binary(a, e) for a in W]...)
sgnE(a, e, s) = (a[1] + s * a[2] * sqrt(e)) > 0 ? 1 : -1

function sqrt_padic(e, p, k)
    r = BigInt(findfirst(x -> mod(x * x - e, p) == 0, 1:p-1))
    m = BigInt(p)
    for _ in 1:k
        m *= p
        r = mod(r - (r * r - e) * invmod(2r, m), m)
    end
    return r, m
end

"(a,b)_p for p odd, a, b p-adic integers known modulo m = p^k"
function hilb_Zp(a, b, p, m)
    function vu(x)
        x = mod(x, m); @assert x != 0
        v = 0
        while x % p == 0; x = div(x, p); v += 1; end
        return v, mod(x, p)
    end
    al, u = vu(a); be, v = vu(b)
    r = 1
    (isodd(al) && isodd(be) && p % 4 == 3) && (r = -r)
    isodd(be) && (r *= legendre(u, p))
    isodd(al) && (r *= legendre(v, p))
    return r
end

"residue of a rational with p-free denominator"
resp(x::Rational{BigInt}, p) = mod(numerator(x) * invmod(denominator(x), p), p)

"valuation (uniformiser of valuation 1) and residue class of the unit part of a in E_P, p odd, nonsplit"
function val_unit_nonsplit(a, e, p)
    u, v = BigInt(a[1]), BigInt(a[2])
    if e % p != 0                       # inert: uniformiser p, residue field F_p[sqrt e]
        k = 0
        while u % p == 0 && v % p == 0; u = div(u, p); v = div(v, p); k += 1; end
        return k, (mod(u, p), mod(v, p))
    end
    U_ = Rational{BigInt}(u); V_ = Rational{BigInt}(v); k = 0     # ramified: uniformiser sqrt e
    while true
        if numerator(U_) % p != 0
            return k, (resp(U_, p), 0)
        end
        U_, V_ = V_, U_ / e             # a / sqrt e = v + (u/e) sqrt e
        @assert denominator(U_) % p != 0 && denominator(V_) % p != 0
        k += 1
    end
end
fq_mul(x, y, e, p) = (mod(x[1] * y[1] + e * x[2] * y[2], p), mod(x[1] * y[2] + x[2] * y[1], p))
function fq_pow(x, n, e, p)
    r = (BigInt(1), BigInt(0))
    while n > 0
        isodd(n) && (r = fq_mul(r, x, e, p))
        x = fq_mul(x, x, e, p); n >>= 1
    end
    return r
end
"tame symbol over E_P, p odd nonsplit in E"
function hilb_nonsplit(a, b, e, p)
    q = e % p != 0 ? p * p : p
    va, ua = val_unit_nonsplit(a, e, p); vb, ub = val_unit_nonsplit(b, e, p)
    t = fq_mul(fq_pow(ua, vb, e, p), fq_pow(fq_pow(ub, va, e, p), q - 2, e, p), e, p)
    isodd(va * vb) && (t = (mod(-t[1], p), mod(-t[2], p)))
    r = fq_pow(t, div(q - 1, 2), e, p)
    @assert r == (1, 0) || r == (p - 1, 0)
    return r == (1, 0) ? 1 : -1
end
issplitE(e, p) = e % p != 0 && legendre(e, p) == 1
"prod over P | p of inv_P C^+(W), W = <a,b,c>, as a sign: C^+(W) = (-ab, -ac); p odd"
function inv_product(W, e, p)
    a, b, c = W
    x = negE(mulE(a, b, e)); y = negE(mulE(a, c, e))
    if issplitE(e, p)
        s, m = sqrt_padic(e, p, 40)
        return prod(hilb_Zp(x[1] + sg * s * x[2], y[1] + sg * s * y[2], p, m) for sg in (1, -1))
    end
    return hilb_nonsplit(x, y, e, p)
end

function main()
    C = Checks("k3_witt_index.jl")

    # ---- rank 5 (Lemma lem:witt(i), Corollary cor:rho17) ----
    vals = [1, 2, 3, 5, 6, 7, 10, 14, 23, 46, 69]
    cnt = 0; ok = true
    for a in vals, b in vals, c in vals, e_ in vals, f in vals
        (c <= e_ <= f) || continue
        T = [a, b, -c, -e_, -f]
        ok &= some_m(T, union(Set(primes_of(a * b * c * e_ * f)), Set([2]))) !== nothing
        cnt += 1
    end
    check(C, "rank 5, signature (2,3): all $cnt diagonal forms <a,b,-c,-e,-f> (entries in $vals) embed in U^3+<-m>, m > 0 (expected 34606)",
          ok && cnt == 34606)
    check(C, "rank 5 recipe: T = U + <x,y,z> with x > 0 > y, z gives T + <-x,-y> = U^3 + <z>, on 2000 random isotropic forms", begin
        rng = MersenneTwister(5); good = true
        for _ in 1:2000
            x = rand(rng, 1:40); y = -rand(rng, 1:40); z = -rand(rng, 1:40)
            T = vcat(U, [x, y, z])
            good &= isometric(vcat(T, [-x, -y]), vcat(U3, [z])) && embeds(T, vcat(U3, [-sqfree(-z)]))
        end
        good end)
    check(C, "<1,1,-1,-23,-23> and <1,1,-1,-23,-46> embed with m = 23 (they fail m = 1)",
          some_m([1, 1, -1, -23, -23], [2, 23]) == 23 && some_m([1, 1, -1, -23, -46], [2, 23]) == 23 &&
          !embeds([1, 1, -1, -23, -23], vcat(U3, [-1])))
    check(C, "<2,2,-6,-6>, <2,2,-2,-6,-6>, <2,6,-2,-2,-2> embed in U^3 + <-1> (m = 1)",
          all(some_m(T, [2, 3]) == 1 for T in ([2, 2, -6, -6], [2, 2, -2, -6, -6], [2, 6, -2, -2, -2])))
    check(C, "no rank-7 space of signature (2,5) embeds in U^3+<-m>, m in 1..60 (signature)",
          !any(embeds([1, 1, -1, -1, -1, -1, -1], vcat(U3, [-m])) for m in 1:60))

    # ---- rank 6 (Lemma lem:witt(ii), Corollary cor:rho16) ----
    vals6 = [1, 2, 3, 5, 6, 7, 10, 23]
    n = 0; cov = 0; agree = true
    for a in 1:3, b in a:3
        for x1 in vals6, x2 in vals6, x3 in vals6, x4 in vals6
            (x1 <= x2 <= x3 <= x4) || continue
            T = [a, b, -x1, -x2, -x3, -x4]
            w2 = witt2_rank6(T); lm = find_lam_m(T)
            agree &= (lm !== nothing) == w2
            # (a) <=> exists m: test directly with the m supported on the primes of T and lam
            n += 1; cov += w2
        end
    end
    check(C, "rank 6: $n diagonal forms (expected 1980); local criterion (d) agrees with T ~ lam(U^2+<-1,-d>), lam < 3000, on all", agree && n == 1980)
    check(C, "rank 6: $cov of Witt index 2, $(n - cov) of Witt index 1 (expected 1484 and 496)", cov == 1484 && n - cov == 496)
    for (T, want) in (([1, 1, -1, -1, -7, -7], (7, 7)), ([1, 1, -1, -1, -5, -23], (5, 23)), ([1, 1, -1, -1, -7, -23], (7, 23)))
        check(C, "$T: Witt index 2 with (lam, m) = $want", witt2_rank6(T) && find_lam_m(T) == want)
    end
    check(C, "Witt index 1 examples <1,1,-1,-2,-3,-3>, <1,1,-1,-2,-5,-10> embed in no U^3+<-m>, m squarefree <= 2000",
          all(!witt2_rank6(T) && !any(embeds(T, vcat(U3, [-m])) for m in SQF if m <= 2000)
              for T in ([1, 1, -1, -2, -3, -3], [1, 1, -1, -2, -5, -10])))

    # ---- the tame symbol (Theorem thm:rmcrit) ----
    rng = MersenneTwister(3); good = true
    for e in (2, 3, 5, 6, 7, 10), p in (3, 5, 7, 11, 13)
        issplitE(e, p) && continue
        for _ in 1:150
            a = (rand(rng, -9:9), rand(rng, -9:9)); b = (rand(rng, -9:9), rand(rng, -9:9)); c = (rand(rng, -9:9), rand(rng, -9:9))
            (Nm(a, e) == 0 || Nm(b, e) == 0 || Nm(c, e) == 0) && continue
            good &= hilb_nonsplit(a, negE(a), e, p) == 1
            om = (1 - a[1], -a[2]); Nm(om, e) != 0 && (good &= hilb_nonsplit(a, om, e, p) == 1)
            good &= hilb_nonsplit(mulE(a, b, e), c, e, p) == hilb_nonsplit(a, c, e, p) * hilb_nonsplit(b, c, e, p)
            x = rand(rng, (-1, 1)) * rand(rng, 1:60)
            good &= hilb_nonsplit((x, 0), b, e, p) == hilbert(x, Nm(b, e), p)
        end
    end
    check(C, "tame symbol over E_P (p odd nonsplit): (a,-a) = 1, (a,1-a) = 1, bimultiplicativity, projection formula (x,y)_P = (x,Ny)_p", good)

    # ---- Theorem thm:rmcrit on random W ----
    NS = 1000
    totn = 0; totchk = 0; okall = true; counts = Dict{Int,Tuple{Int,Int}}()
    for e in (2, 3, 5, 6, 7, 10, 13)
        els = [(u, v) for u in -4:4 for v in -4:4 if (u, v) != (0, 0) && Nm((u, v), e) != 0]
        pos1 = [a for a in els if sgnE(a, e, 1) > 0 && sgnE(a, e, -1) < 0]
        negb = [a for a in els if sgnE(a, e, 1) < 0 && sgnE(a, e, -1) < 0]
        r = MersenneTwister(100 + e); cv = 0
        for _ in 1:NS
            W = (rand(r, pos1), rand(r, pos1), rand(r, negb))
            T = trace_form(W, e)
            okall &= sig(T) == (2, 4)
            dl = mulE(mulE(W[1], W[2], e), W[3], e); d = disc(T)
            okall &= d == sqfree(e * Nm(dl, e)) && d > 0
            ps = [p for p in relevant_primes(T) if is_square_Qp(-d, p)]
            w2 = all(hasse(T, p) == hasse(U3, p) for p in ps)
            for p in ps
                p == 2 && continue
                okall &= (hasse(T, p) == hasse(U3, p)) == (inv_product(W, e, p) == 1)
                totchk += 1
            end
            okall &= w2 == (find_lam_m(T) !== nothing)
            cv += w2; totn += 1
        end
        counts[e] = (cv, NS - cv)
    end
    check(C, "Theorem thm:rmcrit: on $totn random W (1000 for each e in 2,3,5,6,7,10,13) the criterion sum_P inv_P C^+(W) = 0 agrees with the Hasse invariant of Tr W at all $totchk pairs (W, odd p), and Witt index 2 iff T ~ lam(U^2+<-1,-d>)", okall)
    println("    counts (Witt index 2, Witt index 1): ", sort(collect(counts)))
    check(C, "every e has W of both kinds; the share of Witt index 1 lies between 15% and 45%",
          all(0.15 * NS <= counts[e][2] <= 0.45 * NS for e in keys(counts)))

    # ---- Corollary cor:rmopen: the table ----
    tab = [(2, ((3, 3), (2, 4), (-3, 2)), 14, 3), (3, ((2, 4), (0, 3), (-1, 0)), 11, 3),
           (5, ((-1, 1), (2, 1), (-4, 1)), 55, 2), (6, ((-3, 2), (0, 3), (-4, 0)), 15, 2),
           (7, ((0, 2), (3, 3), (-1, 0)), 6, 7)]
    for (e, W, dd, pf) in tab
        T = trace_form(W, e); d = disc(T)
        signs = sgnE(W[1], e, 1) + sgnE(W[2], e, 1) + sgnE(W[3], e, 1) == 1 &&
                all(sgnE(a, e, -1) < 0 for a in W)
        ps = [p for p in relevant_primes(T) if is_square_Qp(-d, p)]
        bad = [p for p in ps if hasse(T, p) != hasse(U3, p)]
        crit = pf == 2 || inv_product(W, e, pf) == -1
        check(C, "table: e = $e, W = $W: signature (2,1)/(0,3), d = $dd, Tr W of Witt index 1, failing exactly at p = $pf" *
              (pf == 2 ? "" : ", and sum_P inv_P C^+(W) != 0 there"),
              signs && sig(T) == (2, 4) && d == dd && bad == [pf] && !witt2_rank6(T) && crit)
    end

    # ---- Corollary cor:rmcovered and the density step of Theorem thm:densecurves ----
    good = true
    for e in (2, 3, 5, 6, 7, 10, 13, 17, 21), s1 in (1, 2, 3, 5, 7), s2 in (1, 2, 3, 5, 7)
        for c in ((-1, 0), (-3, 1), (-5, -1), (-7, 2))
            (sgnE(c, e, 1) < 0 && sgnE(c, e, -1) < 0) || continue
            W = ((0, s1), (0, s2), c)
            T = trace_form(W, e)
            good &= T[1:4] == vcat(U, U) && sig(T) == (2, 4) && witt2_rank6(T) && find_lam_m(T) !== nothing
        end
    end
    check(C, "W = <s1 sqrt e, s2 sqrt e, c>, c totally negative: Tr W = U^2 + Tr<c>, Witt index 2, embeds in U^3+<-m>", good)
    finish(C)
end
main()
