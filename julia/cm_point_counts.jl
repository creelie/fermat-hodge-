# Counting bounds for the convolutions at the CM point A_0 = E_0^6 (Lemmas VI.8, VI.9, VI.12 and Table III).
# Julia port of code/cm_point_counts.py; same pieces, same Ext dimensions, same bounds, same numbers.
#
# Pieces: O_{Z_zeta} (x) L^k [s] for the 32 abelian threefolds Z_zeta = C_{zeta_1} x C_{zeta_2} x C_{zeta_3},
# zeta in mu_4^3 with prod zeta = +-1, and L^l [t].  The polarised criterion asks dim Ext^2(E, E) = 57.
# Two lower bounds for dim Ext^2(E, E), valid for every order of the pieces and every twisted differential:
#   (1) C^2 - C^1 - C^3, where C^j is the dimension of the total-degree-j part of the E_1 page;
#   (2) the safe (isolated) classes: a class in Ext^k(P_a, P_b) of total degree 2 can be hit only from a
#       block (a'', b'') of total degree 1 with a ~> a'' and b'' ~> b in the graph of possible
#       Maurer-Cartan components, and can map only into a block (a', b') of total degree 3 with a' ~> a
#       and b ~> b'; a class with neither survives.
# For two threefolds meeting along a curve or a surface only the E_2 page is known; its dimensions are
# upper bounds for C^1 and C^3 and the degree-2 classes of those blocks are not counted as safe.
# The Chern character is computed exactly in the Hodge ring of A_0 (exterior algebra on dz_j, dzbar_j
# with Gaussian rational coefficients) and a configuration is kept only when ch(E) has the polarised
# shape N (alpha + alphabar) + sum c_m theta^m with N != 0.
#
#   julia --startup-file=no cm_point_counts.jl
#
# Exact arithmetic: Gaussian rationals as pairs of Rational{Int} (the arithmetic of Rational{Int} in
# Julia is overflow-checked: it throws instead of wrapping); no packages.

module CMPointCounts

export Gq, Form, Piece, ZERO, ONE, IMAG, MU4, ZETAS, THETA, WEIL, ALPHA, ALPHABAR, fadd, fmul, fscale,
       z_class, piece_ch, polarised, ext_dims, zmeet, zsign, base, bounds, configuration_ch, Lpiece, Zpiece

# -- Gaussian rationals and the exterior algebra on 12 generators ---------------------------------------
struct Gq
    re::Rational{Int}
    im::Rational{Int}
end
Gq(x::Integer) = Gq(x // 1, 0 // 1)
const ZERO = Gq(0)
const ONE = Gq(1)
const IMAG = Gq(0 // 1, 1 // 1)
Base.:+(a::Gq, b::Gq) = Gq(a.re + b.re, a.im + b.im)
Base.:-(a::Gq, b::Gq) = Gq(a.re - b.re, a.im - b.im)
Base.:-(a::Gq) = Gq(-a.re, -a.im)
Base.:*(a::Gq, b::Gq) = Gq(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)
Base.:*(a::Gq, r::Rational{Int}) = Gq(a.re * r, a.im * r)
Base.conj(a::Gq) = Gq(a.re, -a.im)
Base.:/(a::Gq, b::Gq) = (a * conj(b)) * (1 // (b.re^2 + b.im^2))
Base.iszero(a::Gq) = a.re == 0 && a.im == 0

const Form = Dict{Int,Gq}        # bit mask of generators -> coefficient; generators 0..5 dz_j, 6..11 dzbar_j

"sign of reordering the generators of m1 then m2 into increasing order"
function wedge_sign(m1::Int, m2::Int)
    s = 0
    for i in 0:11
        if (m2 >> i) & 1 == 1
            s += count_ones(m1 >> (i + 1))
        end
    end
    return isodd(s) ? -1 : 1
end

function fmul(f::Form, g::Form)
    out = Form()
    for (m1, c1) in f, (m2, c2) in g
        m1 & m2 != 0 && continue
        c = c1 * c2
        wedge_sign(m1, m2) < 0 && (c = -c)
        m = m1 | m2
        out[m] = get(out, m, ZERO) + c
    end
    return filter!(p -> !iszero(p.second), out)
end

function fadd(f::Form, g::Form, cg::Gq=ONE)
    out = copy(f)
    for (m, c) in g
        out[m] = get(out, m, ZERO) + c * cg
    end
    return filter!(p -> !iszero(p.second), out)
end

fscale(f::Form, c::Gq) = filter!(p -> !iszero(p.second), Form(m => v * c for (m, v) in f))

"(i/2) dz_p ^ dzbar_q, p, q in 0..5"
gen2(p, q) = Form((1 << p) | (1 << (6 + q)) => Gq(0 // 1, 1 // 2))

const A = [gen2(j, j) for j in 0:2]
const B = [gen2(3 + j, 3 + j) for j in 0:2]
const C = [gen2(j, 3 + j) for j in 0:2]
const CB = [gen2(3 + j, j) for j in 0:2]
const THETA = let t = Form()
    for j in 1:3
        t = fadd(fadd(t, A[j]), B[j])
    end
    t
end
const MU4 = [ONE, IMAG, Gq(-1), Gq(0 // 1, -1 // 1)]
const ALPHA = fmul(fmul(C[1], C[2]), C[3])
const ALPHABAR = fmul(fmul(CB[1], CB[2]), CB[3])
const WEIL = fadd(ALPHA, ALPHABAR)
const THETA_POW = let v = [Form(0 => ONE)]
    for _ in 1:6
        push!(v, fmul(v[end], THETA))
    end
    v
end

# a point zeta of mu_4^3 is a triple of exponents (e_1, e_2, e_3), zeta_j = i^(e_j)
const Zeta = NTuple{3,Int}

curve_class(j::Int, zeta::Gq) = fadd(fadd(fadd(A[j], B[j]), fscale(C[j], conj(zeta))), fscale(CB[j], zeta))

function z_class(z::Zeta)
    f = curve_class(1, MU4[z[1]+1])
    for j in 2:3
        f = fmul(f, curve_class(j, MU4[z[j]+1]))
    end
    return f
end

function exp_theta(k::Int)
    f = Form()
    for m in 0:6
        f = fadd(f, THETA_POW[m+1], Gq(k^m // factorial(m), 0 // 1))
    end
    return f
end

"Is ch = N (alpha + alphabar) + sum_m c_m theta^m ?  Returns (yes, N, c)."
function polarised(ch::Form)
    key = first(keys(ALPHA))
    N = get(ch, key, ZERO) / WEIL[key]
    rest = fadd(ch, WEIL, -N)
    cs = Gq[]
    for m in 0:6
        part = Form(b => c for (b, c) in rest if count_ones(b) == 2m)
        tp = THETA_POW[m+1]
        if isempty(part)
            push!(cs, ZERO)
            continue
        end
        b0, c0 = first(tp)
        haskey(part, b0) || return false, N, cs
        lam = part[b0] / c0
        isempty(fadd(part, tp, -lam)) || return false, N, cs
        push!(cs, lam)
    end
    return true, N, cs
end

# -- the pieces and their Ext groups --------------------------------------------------------------------
# the order of itertools.product(MU4, repeat = 3) with MU4 = [1, i, -1, -i]
const ZETAS = [(a, b, c) for a in 0:3 for b in 0:3 for c in 0:3 if iseven(a + b + c)]
@assert length(ZETAS) == 32
const CHI_Z = 8                                   # chi_{Z_zeta} = 8

zsign(z::Zeta) = mod(sum(z), 4) == 0 ? 1 : -1

"(d, D): d = number of shared coordinates, D = number of components of Z cap Z'"
function zmeet(z::Zeta, z2::Zeta)
    d, D = 0, 1
    for j in 1:3
        if z[j] == z2[j]
            d += 1
        else
            diff = MU4[z[j]+1] - MU4[z2[j]+1]
            D *= Int(diff.re^2 + diff.im^2)
        end
    end
    return d, D
end

struct Piece
    kind::Symbol          # :Z or :L
    zeta::Zeta            # (-1, -1, -1) for a line bundle
    twist::Int
    shift::Int
end
Lpiece(twist, shift) = Piece(:L, (-1, -1, -1), twist, shift)
Zpiece(zeta, twist, shift) = Piece(:Z, zeta, twist, shift)

const CH_CACHE = Dict{Tuple{Symbol,Zeta,Int,Int},Form}()
"Chern character of a piece (cached by kind, zeta, twist and the parity of the shift)"
function piece_ch(p::Piece)
    get!(CH_CACHE, (p.kind, p.zeta, p.twist, mod(p.shift, 2))) do
        f = exp_theta(p.twist)
        p.kind == :Z && (f = fmul(z_class(p.zeta), f))
        fscale(f, Gq(iseven(p.shift) ? 1 : -1))
    end
end

function Base.show(io::IO, p::Piece)
    if p.kind == :L
        print(io, "L^", p.twist, "[", p.shift, "]")
    else
        print(io, "O_Z", join("1i-j"[e+1] for e in p.zeta), "L^", p.twist, "[", p.shift, "]")
    end
end

const EXT_CACHE = Dict{Tuple{Symbol,Zeta,Symbol,Zeta,Int},Tuple{Dict{Int,Int},Bool}}()
"Dimensions of Ext^k(p, q) by degree k (Lemmas VI.8 and VI.9).  The flag says whether the numbers are
exact (true) or E_2 upper bounds (false)."
function ext_dims(p::Piece, q::Piece)
    get!(EXT_CACHE, (p.kind, p.zeta, q.kind, q.zeta, q.twist - p.twist)) do
        ext_dims_raw(p, q)
    end
end

function ext_dims_raw(p::Piece, q::Piece)
    m = q.twist - p.twist
    if p.kind == :L && q.kind == :L
        m > 0 && return Dict(0 => m^6), true
        m < 0 && return Dict(6 => m^6), true
        return Dict(k => binomial(6, k) for k in 0:6), true
    end
    if p.kind == :Z && q.kind == :L
        m > 0 && return Dict(3 => CHI_Z * m^3), true
        m < 0 && return Dict(6 => CHI_Z * (-m)^3), true
        return Dict(k => binomial(3, k - 3) for k in 3:6), true
    end
    if p.kind == :L && q.kind == :Z
        m > 0 && return Dict(0 => CHI_Z * m^3), true
        m < 0 && return Dict(3 => CHI_Z * (-m)^3), true
        return Dict(k => binomial(3, k) for k in 0:3), true
    end
    # two threefolds
    if p.zeta == q.zeta
        m > 0 && return Dict(k => binomial(3, k) * CHI_Z * m^3 for k in 0:3), true
        m < 0 && return Dict(k => binomial(3, k - 3) * CHI_Z * (-m)^3 for k in 3:6), true
        return Dict(k => binomial(6, k) for k in 0:6), true
    end
    d, D = zmeet(p.zeta, q.zeta)
    d == 0 && return Dict(3 => D), true
    c = 3 - d
    # E_2^{p,q} = H^p(W, O_W^{C(d, q-c)} (x) L^m|_W); W = D translates of an abelian d-fold with
    # (theta|_W)^d / d! = 2^d; ample: H^0 only, chi = (2m)^d; anti-ample: H^d only; trivial: all H^p.
    out = Dict{Int,Int}()
    if m > 0
        for q_ in c:3
            out[q_] = get(out, q_, 0) + D * binomial(d, q_ - c) * (2m)^d
        end
    elseif m < 0
        for q_ in c:3
            out[q_+d] = get(out, q_ + d, 0) + D * binomial(d, q_ - c) * (2 * (-m))^d
        end
    else
        for q_ in c:3, p_ in 0:d
            out[p_+q_] = get(out, p_ + q_, 0) + D * binomial(d, q_ - c) * binomial(d, p_)
        end
    end
    return out, false
end

function bounds(pieces::Vector{Piece})
    n = length(pieces)
    @assert n <= 64
    tot = Dict{Int,Int}()
    deg2_exact = zeros(Int, n, n)             # exact dimension of the total-degree-2 classes of the block (a, b)
    has2 = falses(n, n)
    edge = falses(n, n)
    deg1 = falses(n, n); deg3 = falses(n, n)
    for a in 1:n, b in 1:n
        pa, pb = pieces[a], pieces[b]
        dims, exact = ext_dims(pa, pb)
        for (k, dim) in dims
            t = k + pb.shift - pa.shift
            tot[t] = get(tot, t, 0) + dim
            if t == 2 && exact
                deg2_exact[a, b] += dim; has2[a, b] = true
            end
            t == 1 && a != b && (edge[a, b] = true)
            t == 1 && (deg1[a, b] = true)
            t == 3 && (deg3[a, b] = true)
        end
    end
    # reachability a ~> b (including a == b)
    reach = [a == b || edge[a, b] for a in 1:n, b in 1:n]
    for k in 1:n, a in 1:n
        if reach[a, k]
            for b in 1:n
                reach[k, b] && (reach[a, b] = true)
            end
        end
    end
    safe = 0
    for a in 1:n, b in 1:n
        has2[a, b] || continue
        hit = false
        for a2 in 1:n, b2 in 1:n
            if deg1[a2, b2] && reach[a, a2] && reach[b2, b] && (a2, b2) != (a, b)
                hit = true; break
            end
        end
        hit && continue
        out = false
        for a2 in 1:n, b2 in 1:n
            if deg3[a2, b2] && reach[a2, a] && reach[b, b2] && (a2, b2) != (a, b)
                out = true; break
            end
        end
        out || (safe += deg2_exact[a, b])
    end
    c1, c2, c3 = get(tot, 1, 0), get(tot, 2, 0), get(tot, 3, 0)
    return (C1=c1, C2=c2, C3=c3, euler=c2 - c1 - c3, safe=safe, lower=max(c2 - c1 - c3, safe))
end

function configuration_ch(pieces::Vector{Piece})
    ch = Form()
    for p in pieces
        ch = fadd(ch, piece_ch(p))
    end
    ok, N, _ = polarised(ch)
    return ok && !iszero(N), (N.im == 0 && denominator(N.re) == 1) ? Int(N.re) : 0
end

"The thirty-two threefolds at one twist, shifts of the parity of prod zeta."
base(twist::Int=0, shift0::Int=0) = [Zpiece(z, twist, shift0 + (zsign(z) == 1 ? 0 : 1)) for z in ZETAS]

function sum_classes()
    f = Form()
    for z in ZETAS
        f = fadd(f, z_class(z), Gq(zsign(z)))
    end
    return f
end

"the Cartesian product of r copies of vals, last entry fastest"
function product_each(f, vals, r::Int)
    idx = ones(Int, r)
    while true
        f([vals[i] for i in idx])
        j = r
        while j >= 1 && idx[j] == length(vals)
            idx[j] = 1; j -= 1
        end
        j == 0 && break
        idx[j] += 1
    end
end

function combinations(vals, r::Int)
    out = Vector{eltype(vals)}[]
    function rec(start, cur)
        if length(cur) == r
            push!(out, copy(cur)); return
        end
        for i in start:length(vals)
            push!(cur, vals[i]); rec(i + 1, cur); pop!(cur)
        end
    end
    rec(1, eltype(vals)[])
    return out
end

function main()
    npass = 0; nfail = 0
    function check(name, ok)
        println(ok ? "PASS " : "FAIL ", name)
        ok ? (npass += 1) : (nfail += 1)
    end
    show_b(b) = "C1=$(b.C1) C2=$(b.C2) C3=$(b.C3) euler=$(b.euler) safe=$(b.safe) lower=$(b.lower)"
    L3(ts) = [Lpiece(l, t) for (l, t) in zip((1, 2, 3), ts)]

    check("S(1) - S(-1) = 32 (alpha + alphabar)", sum_classes() == fscale(WEIL, Gq(32)))
    check("theta (alpha + alphabar) = 0", isempty(fmul(THETA, WEIL)))

    # (0) the 35 pieces: three line bundles at twists above the threefolds
    safe35 = Int[]
    for ts in ((0, 0, 0), (2, 3, 4), (-3, -2, -1))
        pcs = vcat(base(), L3(ts))
        ok, N = configuration_ch(pcs)
        b = bounds(pcs)
        println("  base35 L(1, 2, 3) shifts $ts: ", ok ? "polarised" : "NOT polarised", ", N = $N, ", show_b(b))
        push!(safe35, b.safe)
    end

    # (a) four or five line bundles: twists in 1..4, shifts in the window -3..3
    count_a = 0; best_a = nothing; max_euler = typemin(Int)
    for nL in (4, 5), ls in combinations(collect(1:4), nL)
        product_each(collect(-3:3), nL) do ts
            pcs = vcat(base(), [Lpiece(l, t) for (l, t) in zip(ls, ts)])
            ok, _ = configuration_ch(pcs)
            ok || return
            count_a += 1
            b = bounds(pcs)
            max_euler = max(max_euler, b.euler)
            if best_a === nothing || b.lower < best_a[1]
                best_a = (b.lower, copy(ls), copy(ts), b)
            end
        end
    end
    println("  (a) >= 4 line bundles, twists 1..4, shifts -3..3: $count_a polarised configurations; least lower bound ",
            best_a[1], " at twists ", best_a[2], " shifts ", best_a[3], ", ", show_b(best_a[4]), "; largest C2-C1-C3 $max_euler")

    # (b) a sheaf at two shifts: one extra copy of Z_zeta at shift s + delta
    count_b = 0; best_b = nothing
    for z in ZETAS[1:4], delta in (-3, -2, -1, 1, 2, 3), ts in ((0, 0, 0), (1, 2, 3))
        pcs = vcat(base(), [Zpiece(z, 0, (zsign(z) == 1 ? 0 : 1) + delta)], L3(ts))
        ok, _ = configuration_ch(pcs)
        ok || continue
        count_b += 1
        b = bounds(pcs)
        if best_b === nothing || b.lower < best_b[1]
            best_b = (b.lower, pcs[33], ts, b)
        end
    end
    println("  (b) a sheaf at two shifts: $count_b polarised configurations; least lower bound ",
            best_b === nothing ? "none" : best_b)

    # (c) one threefold at three twists 0 < k' < k'' (pairs with shifts cancelling in ch)
    count_c = 0; best_c = nothing
    z = ZETAS[1]
    for (k1, k2) in combinations(collect(1:3), 2), s1 in -2:2, s2 in -2:2, s1b in -2:2, s2b in -2:2
        extra = [Zpiece(z, k1, s1), Zpiece(z, k1, s1b), Zpiece(z, k2, s2), Zpiece(z, k2, s2b)]
        pcs = vcat(base(), extra, L3((0, 0, 0)))
        ok, _ = configuration_ch(pcs)
        ok || continue
        count_c += 1
        b = bounds(pcs)
        if best_c === nothing || b.lower < best_c[1]
            best_c = (b.lower, extra, b)
        end
    end
    println("  (c) a threefold at three twists (pairs cancelling in ch): $count_c polarised configurations; least ",
            best_c[1], " at [", join(best_c[2], ", "), "], ", show_b(best_c[3]))

    # (d) two threefolds meeting along a surface at the same shift: a cancelling pair of a partner
    count_d = 0; best_d = nothing
    partners = [z2 for z2 in ZETAS if zmeet(z, z2)[1] == 2]
    for z2 in partners
        s = zsign(z) == 1 ? 0 : 1
        for delta in (1, -1)
            extra = [Zpiece(z2, 0, s), Zpiece(z2, 0, s + delta)]
            pcs = vcat(base(), extra, L3((0, 0, 0)))
            ok, _ = configuration_ch(pcs)
            ok || continue
            count_d += 1
            b = bounds(pcs)
            if best_d === nothing || b.lower < best_d[1]
                best_d = (b.lower, extra, b)
            end
        end
    end
    println("  (d) a partner meeting along a surface at the same shift: $count_d polarised configurations; least ",
            best_d[1], " at [", join(best_d[2], ", "), "], ", show_b(best_d[3]))

    # the values of Table III and of the proposition on the counts
    want = [
        (safe35[1], 7213, "thirty-five pieces at shifts 0,0,0"),
        (safe35[2], 2605, "thirty-five pieces at shifts 2,3,4"),
        (safe35[3], 2605, "thirty-five pieces at shifts -3,-2,-1"),
        (count_a, 2401, "(a) polarised configurations"),
        (best_a[1], 0, "(a) least isolated bound"),
        (max_euler, -1, "(a) Euler characteristic negative (max <= -1)"),
        (count_b, 0, "(b) polarised configurations"),
        (count_c, 432, "(c) polarised configurations"),
        (best_c === nothing ? -1 : best_c[1], 0, "(c) least isolated bound"),
        (count_d, 6, "(d) polarised configurations"),
        (best_d === nothing ? -1 : best_d[1], 5325, "(d) least isolated bound"),
    ]
    for (got, expd, name) in want
        check("$name: $got (expected $expd)", occursin("negative", name) ? got <= expd : got == expd)
    end
    println("cm_point_counts.jl: $npass checks passed, $nfail failed")
    return nfail
end

end # module

if abspath(PROGRAM_FILE) == @__FILE__
    exit(CMPointCounts.main() > 0 ? 1 : 0)
end
