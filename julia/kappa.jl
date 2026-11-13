# Theorem thm:indefinite: the example X = E^4, h = e_1+e_2+e_3-e_4 (Pf(h) = -1), K = Q(i), q = 1.
# lambda = exp(i h), alpha = cos h, beta = sin h on X; Orlov's equivalence Phi = (mu_* o (id x Phi_P))^{-1}
# from X x X to X x Xhat computed on cohomology (exterior algebra on 16 generators: a_i, b_i of X in bits 0..7,
# those of the second factor in bits 8..15), exact Rational{BigInt} arithmetic.
# (1) Phi(1x1) = pt_Xhat, Phi(1xpt) = 1, Phi(ptx1) = exp(c1(P)), Phi(ptxpt) = pt_X;
# (2) the degree-two part of exp(-c1(P)/2) ch E, E = Phi(F_1 x F_2^vee), is a multiple of
#     omega = -4(h + h^vee), whose coefficients on the eight elliptic factors have mixed signs;
# (3) for six pairs of secant classes of nonzero rank, kappa(E) = exp(-c1(E)/r) ch E has kappa_1 = 0 and
#     kappa_2 = m omega^2 with m = 1/16, 1/16, 1/8, 5/8, 5/8, 145/8 (the value 2P_0Q_0/r of the proof);
# (4) in the rank-zero case the degree-two part of ch E is a nonzero multiple of omega.
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms

const QQ = Rational{BigInt}
const Form = Dict{UInt32,QQ}
prune(f::Form) = filter(p -> !iszero(p.second), f)
function addf(fs::Vector{Form}, cs)
    out = Form()
    for (f, c) in zip(fs, cs), (k, v) in f
        out[k] = get(out, k, zero(QQ)) + QQ(c) * v
    end
    prune(out)
end
addf(a::Form, b::Form) = addf([a, b], [1, 1])
scal(c, a::Form) = prune(Form(k => QQ(c) * v for (k, v) in a))
function wsign(m1::UInt32, m2::UInt32)
    s = 0; x = m2
    while x != 0
        j = trailing_zeros(x); x &= x - one(UInt32)
        s += count_ones(m1 >> (j + 1))
    end
    isodd(s) ? -1 : 1
end
function mul(A::Form, B::Form, maxdeg=16)
    C = Form()
    for (m1, c1) in A
        d1 = count_ones(m1)
        for (m2, c2) in B
            (m1 & m2 != 0 || d1 + count_ones(m2) > maxdeg) && continue
            m = m1 | m2
            C[m] = get(C, m, zero(QQ)) + wsign(m1, m2) * c1 * c2
        end
    end
    prune(C)
end
deg(A::Form, d) = filter(p -> count_ones(p.first) == d, A)
gen(i) = Form(UInt32(1) << i => one(QQ))
const ONE = Form(UInt32(0) => one(QQ))
function expf(A::Form, maxdeg=16)
    R = copy(ONE); T = copy(ONE); k = 0
    while true
        k += 1; T = scal(QQ(1, k), mul(T, A, maxdeg))
        isempty(T) && break
        R = addf(R, T)
    end
    R
end
function power(A::Form, k)
    R = copy(ONE)
    for _ in 1:k; R = mul(R, A) end
    R
end
tau(A::Form) = Form(m => (iseven(count_ones(m) ÷ 2) ? c : -c) for (m, c) in A)

const EPS = [1, 1, 1, -1]
a(i) = gen(i); b(i) = gen(4 + i); a2(i) = gen(8 + i); b2(i) = gen(12 + i)
h1 = addf([scal(EPS[i+1], mul(a(i), b(i))) for i in 0:3], ones(Int, 4))
h2 = addf([scal(EPS[i+1], mul(a2(i), b2(i))) for i in 0:3], ones(Int, 4))
function cos_sin(h)
    hk = [power(h, k) for k in 0:4]
    addf([hk[1], hk[3], hk[5]], [1, QQ(-1, 2), QQ(1, 24)]), addf([hk[2], hk[4]], [1, QQ(-1, 6)])
end
al1, be1 = cos_sin(h1); al2, be2 = cos_sin(h2)

const c1P = addf([addf(mul(a(i), a2(i)), mul(b(i), b2(i))) for i in 0:3], ones(Int, 4))
const expP = expf(c1P)
const HIGHTOP = UInt32(0xFF00)
function fiber_int_high(A::Form)
    R = Form()
    for (m, c) in A
        (m & HIGHTOP) == HIGHTOP || continue
        lo = m & UInt32(0xFF); R[lo] = get(R, lo, zero(QQ)) + c
    end
    prune(R)
end
# Phi_P on cohomology: hat monomial hm -> c * X-monomial lo; it is a signed monomial bijection
const INV = Dict{UInt32,Tuple{UInt32,QQ}}()
bijective = true
for hm in UInt32(0):UInt32(255)
    img = fiber_int_high(mul(Form(hm << 8 => one(QQ)), expP))
    global bijective &= length(img) == 1
    (lo, c), = collect(img)
    haskey(INV, lo) && (global bijective = false)
    INV[lo] = (hm, 1 / c)
end
function mu_pull(A::Form)
    R = Form()
    for (m, c) in A
        t = Form(UInt32(0) => c)
        for i in 0:15
            (m >> i) & 1 == 1 || continue
            t = mul(t, i < 8 ? addf(gen(i), gen(i + 8)) : gen(i))
        end
        R = addf(R, t)
    end
    R
end
function id_x_PhiP_inv(A::Form)
    R = Form()
    for (m, c) in A
        lo = m & UInt32(0xFF); hi = (m >> 8) & UInt32(0xFF)
        hm, f = INV[hi]; mm = lo | (hm << 8)
        R[mm] = get(R, mm, zero(QQ)) + c * f
    end
    prune(R)
end
Phi(A::Form) = id_x_PhiP_inv(mu_pull(A))
const vol_lo = Form(UInt32(0x00FF) => one(QQ)); const vol_hi = Form(UInt32(0xFF00) => one(QQ))

function ratio(A::Form, B::Form)
    isempty(B) && return nothing
    f = nothing
    for k in union(keys(A), keys(B))
        x = get(A, k, zero(QQ)); y = get(B, k, zero(QQ))
        if iszero(y)
            iszero(x) || return nothing
            continue
        end
        g = x / y
        f === nothing ? (f = g) : (f != g && return nothing)
    end
    f
end
function kappa_data(r1, s1, r2, s2)
    chE = Phi(mul(addf([al1, be1], [r1, s1]), tau(addf([al2, be2], [r2, s2]))))
    r = get(chE, UInt32(0), zero(QQ)); c1 = deg(chE, 2)
    kt = mul(expf(scal(QQ(-1, 2), c1P), 4), chE, 4)
    kap = iszero(r) ? nothing : mul(expf(scal(-1 / r, c1), 4), chE, 4)
    r, chE, deg(kt, 2), kap
end

C = Checks("kappa.jl")
check(C, "Phi_P is a signed monomial bijection on cohomology", bijective && length(INV) == 256)
check(C, "Phi(1x1) = pt_Xhat, Phi(1xpt) = 1, Phi(ptx1) = exp(c1(P)), Phi(ptxpt) = pt_X",
      Phi(ONE) == vol_hi && Phi(vol_hi) == ONE && Phi(vol_lo) == expP && Phi(mul(vol_lo, vol_hi)) == vol_lo)
omega = addf([h1, h2], [-4, -4])
signs = vcat([sign(-4 * e) for e in EPS], [sign(-4 * e) for e in EPS])
check(C, "omega = -4(h + h^vee) has coefficient signs $signs on the eight factors (indefinite)",
      any(>(0), signs) && any(<(0), signs))
tests = [(1, 0, 1, 0), (0, 1, 0, 1), (1, 1, 1, 0), (2, 1, 1, 3), (1, 2, -1, 1), (3, -1, 2, 5)]
expect = [QQ(1, 16), QQ(1, 16), QQ(1, 8), QQ(5, 8), QQ(5, 8), QQ(145, 8)]
om2 = mul(omega, omega)
for (t, m) in zip(tests, expect)
    r, chE, kt1, kap = kappa_data(t...)
    f1 = isempty(kt1) ? QQ(0) : ratio(kt1, omega)
    f = ratio(deg(kap, 4), om2)
    check(C, "(r1,s1,r2,s2)=$t: rank $r, kappa_1 = 0, exp(-c1(P)/2)ch E in degree 2 = $(f1) omega, kappa_2 = $(f) omega^2",
          !iszero(r) && isempty(deg(kap, 2)) && f1 !== nothing && f == m)
end
let (r, chE, kt1, kap) = kappa_data(0, 1, 1, 0)
    f = ratio(deg(chE, 2), omega)
    check(C, "(0,1,1,0): rank 0 and ch_1(E) = $f omega, nonzero", iszero(r) && f !== nothing && !iszero(f))
end
finish(C)
