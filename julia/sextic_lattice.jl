# sextic_lattice.jl -- port of code/sextic_lattice.py and code/sextic_cubic_fields.py
# (Remark VI.41: no exclusion over twelve cubic fields).
#
# For each of the twelve totally real cubic fields F_0 = Q(a) of discriminant
# below 500 (O = Z[a]) and q in {1, k + a} (k the least positive integer with
# k + a totally positive), F = F_0(sqrt(-q)):
#   (A) the coefficients, in the monomial basis of wedge^even H^1(X, Z), of the
#       eight parameter classes of the flat secant space S(0,q)
#           v(c_0, f, g, c_3) = c_0 B0_1 B0_2 B0_3 + sum_j tau_j(f) theta_j prod_{k != j} B0_k
#                             + sum_j tau_j(g) B0_j prod_{k != j} theta_k + c_3 theta_1 theta_2 theta_3,
#       B0_j = 1 - tau_j(q) theta_j^2 / 2, computed modulo three primes that split
#       completely in F_0, rational reconstruction, verified modulo a fourth prime;
#   (B) the lattice L of parameters for which v is integral (dual of the row lattice);
#   (C) the Gram matrix of -chi/8 on L from the closed formula
#           chi(v, v) = -8 (Nm(q) c_0^2 + Tr(Nm(q) f^2 / q) + Tr(q g^2) + c_3^2),
#       which is checked against the direct integral of v^dual v modulo a prime;
#   (D) all classes with -chi <= 24 (none) and with -chi <= 32, their shapes
#       (N_w, r^2, r^3) modulo a prime, and the least -chi on a nonzero class.
# Expected least -chi: 32 for q = 1 over every field, and for q = k + a
#   32, 32, 288, 384, 912, 352, 480, 600, 960, 544, 2400, 1208.
# Exact arithmetic (integers modulo primes below 2^46 with 128-bit products,
# BigInt, Rational{BigInt}).  Differences from the Python, none affecting a
# result: the roots modulo p are split with the deterministic shifts
# a = 0, 1, 2, ... (the Python draws a at random); the test vectors of the
# direct integral come from a fixed linear congruential sequence; the least
# norm is found by enumerating the vectors of norm <= 4, 8, 16, ... until
# one is found and taking the minimum (the Python raises the bound by 1);
# k and the total positivity of q are decided exactly from signs of
# coefficients (the Python uses floating-point roots).
# Run: julia --startup-file=no sextic_lattice.jl [disc ...]
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms: Checks, check, finish

const Q = Rational{BigInt}

# ---------------------------------------------------------------- arithmetic mod p
mulm(a::Int64, b::Int64, p::Int64) = Int64(mod(widemul(a, b), p))
function powm(a::Int64, e::Integer, p::Int64)
    r = Int64(1); a = mod(a, p)
    while e > 0
        isodd(e) && (r = mulm(r, a, p))
        a = mulm(a, a, p); e >>= 1
    end
    return r
end
invm(a::Int64, p::Int64) = powm(a, p - 2, p)
ratm(c::Q, p::Int64) = mulm(Int64(mod(numerator(c), p)), invm(Int64(mod(denominator(c), p)), p), p)

function is_prime(n::Int64)
    n < 2 && return false
    bases = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for q in bases
        n % q == 0 && return n == q
    end
    d, s = n - 1, 0
    while iseven(d); d >>= 1; s += 1; end
    for a in bases
        x = powm(Int64(a), d, n)
        (x == 1 || x == n - 1) && continue
        comp = true
        for _ in 1:s-1
            x = mulm(x, x, n)
            x == n - 1 && (comp = false; break)
        end
        comp && return false
    end
    return true
end

# polynomials mod p, coefficient vectors low -> high
function ptrim!(a)
    while !isempty(a) && a[end] == 0; pop!(a); end
    return a
end
function pmulm(a, b, p)
    (isempty(a) || isempty(b)) && return Int64[]
    r = zeros(Int64, length(a) + length(b) - 1)
    for i in eachindex(a), j in eachindex(b)
        r[i+j-1] = mod(r[i+j-1] + mulm(a[i], b[j], p), p)
    end
    return ptrim!(r)
end
function pdivrem(a, b, p)
    a = copy(a); q = zeros(Int64, max(1, length(a) - length(b) + 1)); iv = invm(b[end], p)
    while length(ptrim!(a)) >= length(b)
        c = mulm(a[end], iv, p); d = length(a) - length(b); q[d+1] = c
        for i in eachindex(b); a[i+d] = mod(a[i+d] - mulm(c, b[i], p), p); end
    end
    return ptrim!(q), a
end
prem(a, m, p) = pdivrem(a, m, p)[2]
function ppowm(base, e, m, p)
    r = Int64[1]; b = prem(base, m, p)
    while e > 0
        isodd(e) && (r = prem(pmulm(r, b, p), m, p))
        b = prem(pmulm(b, b, p), m, p); e >>= 1
    end
    return r
end
function pgcd(a, b, p)
    a, b = ptrim!(copy(a)), ptrim!(copy(b))
    while !isempty(b); a, b = b, prem(a, b, p); end
    iv = invm(a[end], p)
    return [mulm(x, iv, p) for x in a]
end
psub1(t, i, p) = (r = copy(t); while length(r) < i; push!(r, 0); end; r[i] = mod(r[i] - 1, p); ptrim!(r))

"sorted roots mod p of the monic integer polynomial poly (coefficients high to low)"
function roots_mod(poly, p::Int64)
    P = Int64[mod(c, p) for c in reverse(poly)]
    xp = ppowm(Int64[0, 1], p, P, p)
    g = pgcd(P, psub1(xp, 2, p), p)                 # gcd(P, x^p - x)
    roots = Int64[]
    function split(h)
        if length(h) == 2
            push!(roots, mulm(mod(-h[1], p), invm(h[2], p), p)); return
        end
        a = Int64(0)
        while true
            t = psub1(ppowm(Int64[a, 1], (p - 1) >> 1, h, p), 1, p)
            d = isempty(t) ? h : pgcd(h, t, p)
            if 1 < length(d) < length(h)
                split(d); split(pdivrem(h, d, p)[1]); return
            end
            a += 1
        end
    end
    length(g) > 1 && split(g)
    return sort!(roots)
end

function big_primes(poly, count, start::Int64)
    out = Int64[]; n = start
    while length(out) < count
        n += 1
        (is_prime(n) && length(roots_mod(poly, n)) == 3) && push!(out, n)
    end
    return out
end

function sqrt_mod(a::Int64, p::Int64)
    a = mod(a, p)
    a == 0 && return Int64(0)
    powm(a, (p - 1) >> 1, p) != 1 && return nothing
    p % 4 == 3 && return powm(a, (p + 1) >> 2, p)
    q, s = p - 1, 0
    while iseven(q); q >>= 1; s += 1; end
    z = Int64(2)
    while powm(z, (p - 1) >> 1, p) != p - 1; z += 1; end
    m, c, t, r = s, powm(z, q, p), powm(a, q, p), powm(a, (q + 1) >> 1, p)
    while t != 1
        i, tt = 0, t
        while tt != 1; tt = mulm(tt, tt, p); i += 1; end
        b = powm(c, Int64(1) << (m - i - 1), p)
        m, c, t, r = i, mulm(b, b, p), mulm(t, mulm(b, b, p), p), mulm(r, b, p)
    end
    return r
end

# ---------------------------------------------------------------- the cubic field
struct Field
    c2::Int; c1::Int; c0::Int                       # a^3 = -c2 a^2 - c1 a - c0
    pw::Vector{Int}                                 # Tr(a^k), k = 0..2
end
function Field(poly)
    _, c2, c1, c0 = poly
    e1, e2 = -c2, c1
    return Field(c2, c1, c0, [3, e1, e1 * e1 - 2 * e2])
end
function mulv(F::Field, x::Vector{Q}, y::Vector{Q})
    r = zeros(Q, 5)
    for i in 1:3, j in 1:3; r[i+j-1] += x[i] * y[j]; end
    for k in (5, 4)
        c = r[k]; r[k] = 0
        r[k-1] -= F.c2 * c; r[k-2] -= F.c1 * c; r[k-3] -= F.c0 * c
    end
    return r[1:3]
end
trv(F::Field, x::Vector{Q}) = x[1] * F.pw[1] + x[2] * F.pw[2] + x[3] * F.pw[3]
basisv(i) = Q[j == i ? 1 : 0 for j in 1:3]

function matinv(A0::Matrix{Q})
    n = size(A0, 1); A = copy(A0); Iv = Q[i == j ? 1 : 0 for i in 1:n, j in 1:n]
    for c in 1:n
        piv = c - 1 + findfirst(r -> A[r, c] != 0, c:n)
        A[[c, piv], :] = A[[piv, c], :]; Iv[[c, piv], :] = Iv[[piv, c], :]
        iv = 1 / A[c, c]
        A[c, :] *= iv; Iv[c, :] *= iv
        for r in 1:n
            (r != c && A[r, c] != 0) || continue
            f = A[r, c]
            A[r, :] -= f * A[c, :]; Iv[r, :] -= f * Iv[c, :]
        end
    end
    return Iv
end

"exact: do all (real) roots of the monic cubic with these coefficients (high to low) lie in x > 0?"
all_roots_positive(c) = c[2] < 0 && c[3] > 0 && c[4] < 0
"coefficients (high to low) of f(x - k)"
function shift_poly(poly, k)
    r = BigInt[0, 0, 0, 0]; pwr = BigInt[1]            # (x - k)^e, low to high
    for e in 0:3
        c = poly[4-e]
        for (i, v) in enumerate(pwr); r[4-(i-1)] += c * v; end
        pwr = vcat(0, pwr) .- k .* vcat(pwr, 0)
    end
    return r
end
"the least positive integer k with k + a totally positive"
function least_shift(poly)
    k = 1
    while !all_roots_positive(shift_poly(poly, k)); k += 1; end   # roots of f(x - k) are the roots of f plus k
    return k
end

# ---------------------------------------------------------------- exterior algebra mod p
# 12 generators: index(a, i) = 6a + i for u_{ai} (i = 0..2), 6a + 3 + k for w_{ak}, a = 0, 1.
# An element is a vector of 4096 coefficients indexed by the bit mask of the monomial.
const NM = 4096
function ext_sign(ma::Int, mb::Int)                   # parity of the number of pairs (x in ma, y in mb), x > y
    s = 0; m = mb
    while m != 0
        y = trailing_zeros(m); s += count_ones(ma >> (y + 1)); m &= m - 1
    end
    return isodd(s)
end
function ext_mul(A::Vector{Int64}, B::Vector{Int64}, p::Int64)
    R = zeros(Int64, NM)
    ia = findall(!=(0), A); ib = findall(!=(0), B)
    for i in ia, j in ib
        ma, mb = i - 1, j - 1
        ma & mb != 0 && continue
        c = mulm(A[i], B[j], p)
        ext_sign(ma, mb) && (c = mod(-c, p))
        R[(ma|mb)+1] = mod(R[(ma|mb)+1] + c, p)
    end
    return R
end
function ext_add(terms, p::Int64)
    R = zeros(Int64, NM)
    for (coef, A) in terms, i in 1:NM
        A[i] == 0 && continue
        R[i] = mod(R[i] + mulm(mod(coef, p), A[i], p), p)
    end
    return R
end
prod3(xs, p) = ext_mul(ext_mul(xs[1], xs[2], p), xs[3], p)

"the eight parameter classes of S(0,q) mod p, and theta_j, the roots mod p in increasing order"
function classes_mod_p(F::Field, poly, qvec, p::Int64)
    rts = roots_mod(poly, p)
    length(rts) == 3 || return nothing
    T = Q[trv(F, mulv(F, basisv(i), basisv(k))) for i in 1:3, k in 1:3]
    Ti = matinv(T)
    # nu*_k = sum_l Ti[k,l] nu_l; the products nu_i nu*_k in the power basis
    prodv = Dict((i, k) => sum(Ti[k, l] * mulv(F, basisv(i), basisv(l)) for l in 1:3) for i in 1:3, k in 1:3)
    ev(vec, r) = (local acc = Int64(0); for (e, c) in enumerate(vec); acc = mod(acc + mulm(ratm(Q(c), p), powm(r, e - 1, p), p), p); end; acc)
    theta = Vector{Vector{Int64}}()
    for r in rts
        th = zeros(Int64, NM)
        for a in 0:1, i in 0:2, k in 0:2
            c = ev(prodv[(i + 1, k + 1)], r)
            m = (1 << (6a + i)) | (1 << (6a + 3 + k))   # u_{ai} ^ w_{ak}
            th[m+1] = mod(th[m+1] + c, p)
        end
        push!(theta, th)
    end
    one = zeros(Int64, NM); one[1] = 1
    inv2 = invm(Int64(2), p)
    qj = [ev(qvec, r) for r in rts]
    B0 = [ext_add([(Int64(1), one), (mod(-mulm(qj[j], inv2, p), p), ext_mul(theta[j], theta[j], p))], p) for j in 1:3]
    params = Vector{Vector{Int64}}()
    push!(params, prod3(B0, p))
    for l in 0:2          # f = a^l
        push!(params, ext_add([(powm(rts[j], l, p), prod3([k == j ? theta[j] : B0[k] for k in 1:3], p)) for j in 1:3], p))
    end
    for l in 0:2          # g = a^l
        push!(params, ext_add([(powm(rts[j], l, p), prod3([k == j ? B0[j] : theta[k] for k in 1:3], p)) for j in 1:3], p))
    end
    push!(params, prod3(theta, p))
    return params, theta, rts
end

"rational reconstruction of a mod m"
function ratrec(a::BigInt, m::BigInt)
    a = mod(a, m)
    r0, r1, s0, s1 = m, a, big(0), big(1)
    bound = isqrt(m >> 1)
    while r1 > bound
        qq = div(r0, r1)
        r0, r1 = r1, r0 - qq * r1
        s0, s1 = s1, s0 - qq * s1
    end
    (s1 == 0 || abs(s1) > bound) && return nothing
    return s1 > 0 ? r1 // s1 : (-r1) // (-s1)
end

"the matrix (monomials x 8) of the coefficients of the eight classes, over Q"
function coefficient_matrix(F::Field, poly, qvec)
    ps = big_primes(poly, 4, Int64(2)^40)
    per_p = [classes_mod_p(F, poly, qvec, p)[1] for p in ps]
    monos = [m for m in 1:NM if any(P[m] != 0 for P in per_p[1]) || any(P[m] != 0 for P in per_p[2])]
    A = Matrix{Q}(undef, length(monos), 8)
    for (ri, m) in enumerate(monos), col in 1:8
        x, md = big(0), big(1)
        for (p, params) in zip(ps[1:3], per_p[1:3])        # CRT over the first three primes
            c = params[col][m]
            t = mod((c - x) * invmod(md, big(p)), p)
            x += md * t; md *= p
        end
        r = ratrec(x, md)
        r === nothing && error("rational reconstruction failed")
        mod(numerator(r) - per_p[4][col][m] * denominator(r), ps[4]) == 0 || error("check modulo the fourth prime failed")
        A[ri, col] = r
    end
    return monos, A
end

# ---------------------------------------------------------------- lattices
function egcd(a::BigInt, b::BigInt)
    b == 0 && return (abs(a), a >= 0 ? big(1) : big(-1), big(0))
    x0, x1, y0, y1 = big(1), big(0), big(0), big(1)
    while b != 0
        q = fld(a, b)
        a, b = b, a - q * b
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    end
    a < 0 && ((a, x0, y0) = (-a, -x0, -y0))
    return a, x0, y0
end
"Z-basis (echelon) of the lattice spanned by integer rows"
function hnf_rows(rows::Vector{Vector{BigInt}})
    ncol = length(rows[1]); piv = Dict{Int,Vector{BigInt}}()
    for r0 in rows
        r = copy(r0)
        for c in 1:ncol
            r[c] == 0 && continue
            if !haskey(piv, c)
                r[c] < 0 && (r = -r)
                piv[c] = r; break
            end
            b = piv[c]
            a0, b0 = r[c], b[c]
            g, x, y = egcd(b0, a0)
            newb = x .* b .+ y .* r
            newr = div(a0, g) .* b .- div(b0, g) .* r
            newb[c] < 0 && (newb = -newb)
            piv[c] = newb; r = newr
            @assert r[c] == 0
        end
    end
    return [piv[c] for c in sort!(collect(keys(piv)))]
end
"L = {x in Q^8 : A x in Z^N}: the dual of the Z-span of the rows of A; rows of the result are a basis"
function integral_lattice(A::Matrix{Q})
    den = reduce(lcm, denominator.(A); init = big(1))
    rows = [BigInt[numerator(x * den) for x in A[i, :]] for i in 1:size(A, 1) if any(!=(0), A[i, :])]
    R = hnf_rows(rows)
    length(R) == 8 || error("the row lattice has rank $(length(R))")
    Rq = Q[R[i][j] // den for i in 1:8, j in 1:8]
    Ri = matinv(Rq)
    return [Q[Ri[i, j] for i in 1:8] for j in 1:8]      # the columns of Rq^{-1}
end

# ---------------------------------------------------------------- the Euler form, closed formula
"x = (c0, f0, f1, f2, g0, g1, g2, c3), f = sum f_l a^l"
function chi_formula(F::Field, qvec, x)
    f = Q[x[2], x[3], x[4]]; g = Q[x[5], x[6], x[7]]; c0, c3 = Q(x[1]), Q(x[8])
    q = Q.(qvec)
    Mq = [mulv(F, q, basisv(i)) for i in 1:3]
    detq = Mq[1][1] * (Mq[2][2] * Mq[3][3] - Mq[2][3] * Mq[3][2]) - Mq[1][2] * (Mq[2][1] * Mq[3][3] - Mq[2][3] * Mq[3][1]) +
           Mq[1][3] * (Mq[2][1] * Mq[3][2] - Mq[2][2] * Mq[3][1])           # Nm(q)
    trq = trv(F, q); q2 = mulv(F, q, q)
    e2 = (trq * trq - trv(F, q2)) / 2
    adjq = Q[q2[i] - trq * q[i] + (i == 1 ? e2 : 0) for i in 1:3]           # Nm(q)/q
    val = detq * c0 * c0 + trv(F, mulv(F, adjq, mulv(F, f, f))) + trv(F, mulv(F, q, mulv(F, g, g))) + c3 * c3
    return -8 * val
end
function gram(F::Field, qvec, Lb)
    ch = [chi_formula(F, qvec, Lb[i]) for i in 1:8]
    return Q[-(chi_formula(F, qvec, Lb[i] + Lb[j]) - ch[i] - ch[j]) / 16 for i in 1:8, j in 1:8]
end

# ---------------------------------------------------------------- the direct integral (mod p)
function check_chi_direct(F::Field, poly, qvec, Lb; trials = 2)
    p = big_primes(poly, 1, Int64(2)^45)[1]
    params, theta, rts = classes_mod_p(F, poly, qvec, p)
    top = NM                                           # index of the top monomial
    th = ext_add([(Int64(1), t) for t in theta], p)
    t6 = zeros(Int64, NM); t6[1] = 1
    for _ in 1:6; t6 = ext_mul(t6, th, p); end
    vol = mulm(t6[top], invm(Int64(720), p), p)        # orientation: the integral of theta^6/6! is 1
    vol == 0 && return false
    ivol = invm(vol, p)
    seed = 20261021
    for _ in 1:trials
        x = Int[]
        for _ in 1:8
            seed = (1103515245 * seed + 12345) % 2147483648
            push!(x, (seed >> 16) % 7 - 3)
        end
        all(==(0), x) && (x[1] = 1)
        coeffs = sum(x[b] * Lb[b] for b in 1:8)
        v = ext_add([(ratm(coeffs[i], p), params[i]) for i in 1:8], p)
        # the top coefficient of v^dual v, v^dual = (-1)^(deg/2) v on each degree
        val = Int64(0)
        for i in 1:NM
            (v[i] == 0 || v[NM+1-i] == 0) && continue
            ma, mb = i - 1, NM - i
            c = mulm(v[i], v[NM+1-i], p)
            (count_ones(ma) % 4 != 0) && (c = mod(-c, p))
            ext_sign(ma, mb) && (c = mod(-c, p))
            val = mod(val + c, p)
        end
        val = mulm(val, ivol, p)
        ref = chi_formula(F, qvec, coeffs)
        mod(numerator(ref) - val * denominator(ref), p) == 0 || return false
    end
    return true
end

# ---------------------------------------------------------------- shapes, exactly mod p
function shape_prime(poly, qvec, start::Int64)
    n = start
    while true
        n += 1
        is_prime(n) || continue
        rts = roots_mod(poly, n)
        length(rts) == 3 || continue
        ok = true
        for r in rts
            qq = sum(big(c) * big(r)^(e - 1) for (e, c) in enumerate(qvec))
            val = Int64(mod(-qq, n))
            (val == 0 || powm(val, (n - 1) >> 1, n) != 1) && (ok = false)
        end
        ok && return n
    end
end
function rank_mod(M0::Matrix{Int64}, p::Int64)
    M = mod.(M0, p); rk = 0
    for c in 1:size(M, 2)
        piv = findfirst(r -> M[r, c] != 0, rk+1:size(M, 1))
        piv === nothing && continue
        piv += rk
        M[[rk + 1, piv], :] = M[[piv, rk + 1], :]
        iv = invm(M[rk+1, c], p)
        for r in 1:size(M, 1)
            (r != rk + 1 && M[r, c] != 0) || continue
            f = mulm(M[r, c], iv, p)
            for cc in 1:size(M, 2); M[r, cc] = mod(M[r, cc] - mulm(f, M[rk+1, cc], p), p); end
        end
        rk += 1
    end
    return rk
end
"w_eps over F_p with s_j = sqrt(-tau_j(q)); returns N_w, sum A, sum rho, the sum of the ranks of the M slices, r^2, r^3"
function shape_invariants(poly, qvec, coeffs, p::Int64)
    rts = roots_mod(poly, p)
    ev(vec, r) = (local acc = Int64(0); for (e, c) in enumerate(vec); acc = mod(acc + mulm(ratm(Q(c), p), powm(r, e - 1, p), p), p); end; acc)
    s = [sqrt_mod(mod(-ev(qvec, r), p), p) for r in rts]
    c0 = ratm(coeffs[1], p); c3 = ratm(coeffs[8], p)
    fj = [ev(coeffs[2:4], r) for r in rts]; gj = [ev(coeffs[5:7], r) for r in rts]
    bits = [(a1, a2, a3) for a1 in 0:1 for a2 in 0:1 for a3 in 0:1]
    Cc = Dict{NTuple{3,Int},Int64}()
    for a in bits
        k = sum(a)
        Cc[a] = k == 0 ? c0 : k == 3 ? c3 : k == 1 ? fj[findfirst(==(1), a)] : gj[findfirst(==(0), a)]
    end
    inv8 = invm(Int64(8), p)
    sgns = [(e1, e2, e3) for e1 in (1, -1) for e2 in (1, -1) for e3 in (1, -1)]
    w = Dict{NTuple{3,Int},Int64}()
    for eps in sgns
        tot = Int64(0)
        for a in bits
            term = Cc[a]
            for j in 1:3
                a[j] == 1 && (term = mulm(mulm(term, mod(Int64(eps[j]), p), p), invm(s[j], p), p))
            end
            tot = mod(tot + term, p)
        end
        w[eps] = mulm(tot, inv8, p)
    end
    Nw = count(e -> w[e] != 0, sgns)
    A = 0
    for j in 1:3, jj in j+1:3, s1 in (1, -1), s2 in (1, -1)
        A += any(e -> w[e] != 0 && e[j] == s1 && e[jj] == s2, sgns)
    end
    rho = 0
    for j in 1:3
        o = [k for k in 1:3 if k != j]
        Mx = Int64[w[ntuple(k -> k == j ? sg : (k == o[1] ? o1 : o2), 3)] for sg in (1, -1), (o1, o2) in [(1, 1), (1, -1), (-1, 1), (-1, -1)]]
        rho += rank_mod(Mx, p)
    end
    Msum = 0
    for j in 1:3, jp in 1:3
        jp == j && continue
        jpp = 6 - j - jp
        for sgp in (1, -1)
            Mx = Int64[w[ntuple(k -> k == j ? a : (k == jpp ? b : sgp), 3)] for a in (1, -1), b in (1, -1)]
            Msum += rank_mod(Mx, p)
        end
    end
    return Nw, A, rho, Msum, 4A + rho, 8Nw + 2Msum
end

# ---------------------------------------------------------------- short vectors
"all nonzero x in Z^n with x^T G x <= bound, G positive definite rational (Fincke-Pohst, exact rationals)"
function short_vectors(G::Matrix{Q}, bound)
    n = size(G, 1)
    q = zeros(Q, n, n); A = copy(G)
    for i in 1:n
        A[i, i] > 0 || error("the Gram matrix is not positive definite")
        q[i, i] = A[i, i]
        for j in i+1:n; q[i, j] = A[i, j] / A[i, i]; end
        for k in i+1:n, l in k:n
            A[k, l] -= q[i, k] * q[i, l] * q[i, i]; A[l, k] = A[k, l]
        end
    end
    out = Vector{Vector{Int}}(); x = zeros(Int, n)
    function rec(i, rem::Q)
        c = Q(0)
        for j in i+1:n; x[j] != 0 && (c -= q[i, j] * x[j]); end
        r = isqrt(floor(BigInt, rem / q[i, i])) + 1
        lo = floor(BigInt, c) - r; hi = ceil(BigInt, c) + r
        for xi in lo:hi
            d = q[i, i] * (xi - c)^2
            d <= rem || continue
            x[i] = xi
            if i == 1
                any(!=(0), x) && push!(out, copy(x))
            else
                rec(i - 1, rem - d)
            end
        end
        x[i] = 0
    end
    rec(n, Q(bound))
    return out
end
norm_of(G, x) = sum(G[i, j] * x[i] * x[j] for i in eachindex(x), j in eachindex(x))

const FIELDS = [(49, [1, 1, -2, -1]), (81, [1, 0, -3, 1]), (148, [1, -1, -3, 1]), (169, [1, -1, -4, -1]),
                (229, [1, 0, -4, 1]), (257, [1, -1, -4, 3]), (316, [1, -1, -4, 2]), (321, [1, -1, -4, 1]),
                (361, [1, -1, -6, 7]), (404, [1, -1, -5, -1]), (469, [1, -1, -5, 4]), (473, [1, 0, -5, -1])]
const EXPECT = Dict(49 => (32, 32), 81 => (32, 32), 148 => (32, 288), 169 => (32, 384), 229 => (32, 912), 257 => (32, 352),
                    316 => (32, 480), 321 => (32, 600), 361 => (32, 960), 404 => (32, 544), 469 => (32, 2400), 473 => (32, 1208))

"discriminant of x^3 + c2 x^2 + c1 x + c0"
cubic_disc(c2, c1, c0) = c2^2 * c1^2 - 4 * c1^3 - 4 * c2^3 * c0 - 27 * c0^2 + 18 * c2 * c1 * c0

function main()
    C = Checks("sextic_lattice.jl")
    only = [parse(Int, a) for a in ARGS]
    for (D, poly) in FIELDS
        (!isempty(only) && !(D in only)) && continue
        cubic_disc(poly[2], poly[3], poly[4]) == D || error("discriminant of $poly is not $D")
        F = Field(poly)
        k = least_shift(poly)
        for (which, qvec) in enumerate(([1, 0, 0], [k, 1, 0]))
            t0 = time()
            # q totally positive: the roots of the characteristic polynomial f(x - k) of k + a are positive
            which == 2 && (all_roots_positive(shift_poly(poly, k)) || error("q is not totally positive"))
            monos, A = coefficient_matrix(F, poly, qvec)
            Lb = integral_lattice(A)
            direct = check_chi_direct(F, poly, qvec, Lb; trials = 2)
            G = gram(F, qvec, Lb)
            integral = all(x -> denominator(x) == 1, G)
            dens = sort!(unique!([Int(denominator(v)) for row in Lb for v in row]))
            sv24 = short_vectors(G, 3)
            sv32 = short_vectors(G, 4)
            p = shape_prime(poly, qvec, Int64(10)^6)
            tally = Dict{NTuple{4,Int},Int}()
            for x in sv32
                co = sum(x[b] * Lb[b] for b in 1:8)
                chi = chi_formula(F, qvec, co)
                Nw, Asum, rho, Msum, r2, r3 = shape_invariants(poly, qvec, co, p)
                key = (Int(chi), Nw, r2, r3); tally[key] = get(tally, key, 0) + 1
            end
            # least -chi/8 on a nonzero class (at least 4): enumerate norm <= 4, 8, 16, ... and take the minimum
            bound = 4; sv = sv32
            while isempty(sv); bound *= 2; sv = short_vectors(G, bound); end
            least = max(4, Int(minimum(norm_of(G, x) for x in sv)))
            println("disc $D poly $poly q=$qvec: $(length(monos)) monomials; denominators $dens; classes with -chi<=24: $(length(sv24)); ",
                    "with -chi<=32: $(length(sv32)); least -chi = $(8 * least); shapes(chi,N_w,r2,r3): ",
                    join(["$k => $v" for (k, v) in sort!(collect(tally))], ", "), "; ", round(time() - t0, digits = 1), "s")
            check(C, "disc $D, q = $(which == 1 ? "1" : "$k + a"): direct integral agrees, Gram matrix of -chi/8 integral, no class with -chi <= 24, least -chi = $(8 * least) (expected $(EXPECT[D][which]))",
                  direct && integral && isempty(sv24) && 8 * least == EXPECT[D][which])
        end
    end
    finish(C)
end
main()
