# Exact checks for the Ext groups at the CM point E_0^6 and the bookkeeping of cancellations.
# Julia port of code/cm_point_ext.py (fourteen checks).
#
# (A) sum_{p+q=k} C(3,q) C(3,p) = C(6,k).
# (B) The Koszul cochain complex of x_1, x_2, x_3 on Q[x_1, x_2, x_3], graded by polynomial degree minus
#     cohomological degree, has cohomology only in cohomological degree 3 and polynomial degree 0, of
#     dimension one (exact ranks over Q).
# (C) The dimensions of the twisted self-Ext groups agree with the Euler characteristics.
# (D) The degree table for pieces O_Z L^k, O_Z' L^k, L^k (twists 0..3): every closed chain of two pieces
#     has total degree at least three; the closed chains of three pieces of total degree three are
#     exactly the ascending twists of one threefold.
# (E) 5 * 15 = 75, 75 - 57 = 18.
# (F) The identities of Lemma A.1 in the exterior algebra of the real one-forms dx_j, dy_j on E_0^6.
#
#   julia --startup-file=no cm_point_ext.jl
#
# Exact arithmetic: Rational{BigInt} for the ranks, Gaussian rationals as pairs of Rational{Int}
# (overflow-checked in Julia) for the forms; no packages.

module CMPointExt

npass = 0; nfail = 0
function check(name, ok)
    global npass, nfail
    println(ok ? "PASS " : "FAIL ", name)
    ok ? (npass += 1) : (nfail += 1)
end

"rank of an integer matrix by Gaussian elimination over Q"
function rank_exact(M::Matrix{Int})
    A = Rational{BigInt}.(M)
    nr, nc = size(A)
    rk = 0
    for c in 1:nc
        piv = findfirst(r -> A[r, c] != 0, rk+1:nr)
        piv === nothing && continue
        piv += rk
        rk += 1
        A[rk, :], A[piv, :] = A[piv, :], A[rk, :]
        for r in rk+1:nr
            if A[r, c] != 0
                f = A[r, c] / A[rk, c]
                A[r, :] .-= f .* A[rk, :]
            end
        end
        rk == nr && break
    end
    return rk
end

# -- (B) the Koszul complex: C^p_g = Lambda^p (x) Q[x]_{g+p}
monomials(d) = [(a, b, c) for a in 0:d for b in 0:d for c in 0:d if a + b + c == d]
subsets(p) = [S for S in ([], [1], [2], [3], [1, 2], [1, 3], [2, 3], [1, 2, 3]) if length(S) == p]
basis(p, g) = g + p < 0 ? Tuple{Vector{Int},NTuple{3,Int}}[] :
              Tuple{Vector{Int},NTuple{3,Int}}[(S, m) for S in subsets(p) for m in monomials(g + p)]
"matrix of the wedge with sum x_i e_i from C^p_g to C^{p+1}_g"
function differential(p, g)
    src, tgt = basis(p, g), basis(p + 1, g)
    idx = Dict(b => i for (i, b) in enumerate(tgt))
    M = zeros(Int, length(tgt), length(src))
    for (j, (S, m)) in enumerate(src), i in 1:3
        i in S && continue
        T = sort(vcat(S, i))
        sign = (-1)^count(s -> s < i, S)
        mi = ntuple(t -> m[t] + (t == i), 3)
        M[idx[(T, mi)], j] += sign
    end
    return M
end

# -- (F) Gaussian rationals and the exterior algebra on the twelve real one-forms
struct Gq
    re::Rational{Int}
    im::Rational{Int}
end
Gq(x::Integer) = Gq(x // 1, 0 // 1)
Base.:+(a::Gq, b::Gq) = Gq(a.re + b.re, a.im + b.im)
Base.:-(a::Gq) = Gq(-a.re, -a.im)
Base.:*(a::Gq, b::Gq) = Gq(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re)
Base.conj(a::Gq) = Gq(a.re, -a.im)
Base.iszero(a::Gq) = a.re == 0 && a.im == 0
const ZERO = Gq(0); const ONE = Gq(1); const IU = Gq(0 // 1, 1 // 1)
gpow(z::Gq, m::Int) = m == 0 ? ONE : z * gpow(z, m - 1)
abs2q(z::Gq) = z.re^2 + z.im^2

const Form = Dict{Int,Gq}       # bit mask of e_0..e_11 -> coefficient; e_{2j} = dx_j, e_{2j+1} = dy_j (j = 0..5)
function wedge_sign(m1::Int, m2::Int)       # sign of the permutation sorting the generators of m1 followed by those of m2
    s = 0
    for i in 0:11
        (m2 >> i) & 1 == 1 && (s += count_ones(m1 >> (i + 1)))
    end
    return isodd(s) ? -1 : 1
end
function wedge(f::Form, g::Form)
    out = Form()
    for (m1, c1) in f, (m2, c2) in g
        m1 & m2 != 0 && continue
        c = c1 * c2
        wedge_sign(m1, m2) < 0 && (c = -c)
        out[m1|m2] = get(out, m1 | m2, ZERO) + c
    end
    return filter!(p -> !iszero(p.second), out)
end
function add(f::Form, g::Form, cg::Gq=ONE)
    out = copy(f)
    for (k, v) in g
        out[k] = get(out, k, ZERO) + cg * v
    end
    return filter!(p -> !iszero(p.second), out)
end
scale(c::Gq, f::Form) = filter!(p -> !iszero(p.second), Form(k => c * v for (k, v) in f))
one_form(j; conj=false) = Form(1 << (2j) => ONE, 1 << (2j + 1) => (conj ? -IU : IU))        # dz_j or dzbar_j
form(p, q) = scale(Gq(0 // 1, 1 // 2), wedge(one_form(p), one_form(q; conj=true)))          # (i/2) dz_p dzbar_q
function prod(fs...)
    out = Form(0 => ONE)
    for f in fs
        out = wedge(out, f)
    end
    return out
end
"coefficient of the oriented volume form of the factors listed in gens"
function integral(f::Form, gens)
    key = 0
    for j in gens
        key |= (1 << (2j)) | (1 << (2j + 1))
    end
    return get(f, key, ZERO)
end

function main()
    # (A)
    check("binomial identity C(6,k)", all(sum(binomial(3, q) * binomial(3, k - q) for q in 0:k) == binomial(6, k) for k in 0:6))

    # (B)
    coh = Dict{Tuple{Int,Int},Int}()
    for g in -3:3, p in 0:3
        dim = length(basis(p, g))
        rk_out = (p < 3 && dim > 0) ? rank_exact(differential(p, g)) : 0
        rk_in = (p > 0 && dim > 0) ? rank_exact(differential(p - 1, g)) : 0
        h = dim - rk_out - rk_in
        h != 0 && (coh[(p, g)] = h)
    end
    check("Koszul cohomology only in cohomological degree 3, polynomial degree 0, dimension one", coh == Dict((3, -3) => 1))

    # (C) Euler characteristics with Koszul signs
    function chi_pieces(a, b, chiZ)
        m = b - a
        dims = m > 0 ? Dict(k => binomial(3, k) * m^3 * chiZ for k in 0:3) :
               m < 0 ? Dict(k => binomial(3, k - 3) * (-m)^3 * chiZ for k in 3:6) :
               Dict(k => binomial(6, k) for k in 0:6)
        return sum((-1)^k * v for (k, v) in dims), dims
    end
    ok = true
    for chiZ in (1, 2, 5), a in -2:2, b in -2:2
        e, dims = chi_pieces(a, b, chiZ)
        ok &= (e == 0)
        a != b && (ok &= (sum(values(dims)) == 8 * abs(b - a)^3 * chiZ))
    end
    check("Euler characteristics of the self-Ext groups vanish, total rank 8|b-a|^3 chi_Z", ok)

    # (D) degree table
    TW = 0:3
    pieces = vcat([(:Z, k) for k in TW], [(:W, k) for k in TW], [(:L, k) for k in TW])
    "degrees k with Ext^k(F_P, F_Q) != 0, P != Q"
    function degrees(P, Q)
        (t, a), (u, b) = P, Q
        t == :L && u == :L && return b > a ? [0] : [6]
        t == :L && u != :L && return b > a ? [0] : (b < a ? [3] : [0, 1, 2, 3])
        t != :L && u == :L && return b > a ? [3] : (b < a ? [6] : [3, 4, 5, 6])
        t != u && return [3]
        b > a && return [0, 1, 2, 3]
        b < a && return [3, 4, 5, 6]
        error("equal pieces")
    end
    two = minimum(minimum(degrees(P, Q)) + minimum(degrees(Q, P)) for P in pieces for Q in pieces if P != Q)
    check("every two-step chain has total degree >= 3", two >= 3)
    Chain = Tuple{Tuple{Symbol,Int},Tuple{Symbol,Int},Tuple{Symbol,Int},Int,Int,Int}
    found = Set{Chain}()
    for P in pieces, Q in pieces, R in pieces
        (P == Q || Q == R || P == R) && continue
        for k1 in degrees(P, Q), k2 in degrees(Q, R), k3 in degrees(R, P)
            k1 + k2 + k3 == 3 && push!(found, (P, Q, R, k1, k2, k3))
        end
    end
    expected = Set{Chain}()
    for t in (:Z, :W), a in TW, b in TW, c in TW
        a < b < c || continue
        chain = [(t, a), (t, b), (t, c)]; degs = [0, 0, 3]
        for r in 0:2        # the same closed chain read from each of its three pieces
            P, Q, R = circshift(chain, -r); k1, k2, k3 = circshift(degs, -r)
            push!(expected, (P, Q, R, k1, k2, k3))
        end
    end
    check("three-step chains of total degree 3 are exactly the ascending twists of one threefold ($(length(found)) readings)",
          found == expected)
    check("no three-step chain of total degree 3 starts at a line bundle", !any(ch -> ch[1][1] == :L, found))

    # (E)
    check("count at the stopping point: 5*15 = 75 and 75 - 57 = 18", 5 * 15 == 75 && 75 - 57 == 18)

    # (F)
    a = [form(j, j) for j in 0:2]; b = [form(3 + j, 3 + j) for j in 0:2]
    c = [form(j, 3 + j) for j in 0:2]; cb = [form(3 + j, j) for j in 0:2]
    theta = Form()
    for j in 1:3
        theta = add(add(theta, a[j]), b[j])
    end
    theta6 = prod(theta, theta, theta, theta, theta, theta)
    check("theta^6/720 integrates to 1 over E_0^6", integral(theta6, 0:5) == Gq(720))
    alpha = prod(c[1], c[2], c[3]); alphabar = prod(cb[1], cb[2], cb[3])
    check("alpha theta = 0 and alphabar theta = 0", isempty(wedge(alpha, theta)) && isempty(wedge(alphabar, theta)))
    check("a_j = dx_j dy_j and the real and imaginary parts of c_j are real forms",
          a[1] == Form(0b11 => ONE) && all(v -> v.im == 0, values(add(c[1], cb[1]))) &&
          all(v -> v.re == 0, values(add(c[1], cb[1], Gq(-1)))))
    mu4 = [ONE, IU, Gq(-1), -IU]
    curve(j, z) = add(add(add(a[j], b[j]), scale(conj(z), c[j])), scale(z, cb[j]))
    ok = true
    for z in mu4
        for w in mu4
            ok &= (integral(wedge(curve(1, z), curve(1, w)), (0, 3)) == Gq(abs2q(z + (-w)), 0 // 1))
        end
        ok &= (integral(wedge(add(a[1], b[1]), curve(1, z)), (0, 3)) == Gq(2))
    end
    check("[C_zeta][C_zeta'] = |zeta - zeta'|^2 and theta.C_zeta = 2 on B_j", ok)
    threefold(zs) = prod(curve(1, zs[1]), curve(2, zs[2]), curve(3, zs[3]))
    Z1 = threefold((ONE, ONE, ONE)); theta3 = prod(theta, theta, theta)
    check("[Z_zeta] theta^3 = 48, so chi_Z = 8", integral(wedge(Z1, theta3), 0:5) == Gq(48) && 48 ÷ 6 == 8)
    T = Dict{Tuple{Int,Int},Form}()
    for m in 0:3, j in 1:3
        t = Form()
        for z in mu4
            t = add(t, curve(j, z), gpow(z, m))
        end
        T[(m, j)] = t
    end
    expT(m, j) = m == 0 ? scale(Gq(4), add(a[j], b[j])) : m == 1 ? scale(Gq(4), c[j]) : m == 2 ? Form() : scale(Gq(4), cb[j])
    check("T_{m,j} = 4(a_j+b_j), 4c_j, 0, 4cbar_j for m = 0,1,2,3", all(T[(m, j)] == expT(m, j) for m in 0:3 for j in 1:3))
    Splus = Form(); Sminus = Form(); n32 = 0
    for z1 in mu4, z2 in mu4, z3 in mu4
        w = z1 * z2 * z3
        if w == ONE
            Splus = add(Splus, threefold((z1, z2, z3))); n32 += 1
        elseif w == Gq(-1)
            Sminus = add(Sminus, threefold((z1, z2, z3))); n32 += 1
        end
    end
    lhs = add(Splus, Sminus, Gq(-1)); rhs = scale(Gq(32), add(alpha, alphabar))
    check("S(1) - S(-1) = 32 (alpha + alphabar), thirty-two threefolds", lhs == rhs && n32 == 32)

    println("cm_point_ext.jl: $npass checks passed, $nfail failed")
    return nfail
end

end # module

if abspath(PROGRAM_FILE) == @__FILE__
    exit(CMPointExt.main() > 0 ? 1 : 0)
end
