# r4_gamma.jl -- Hodge classes on X^a x Z_K^b x E^c at a non-CM point (Theorems thm:tensordecomp, thm:gammalink).
# Mumford-Tate group of X x Z_K x E at a non-CM point: G x T, G = SL_2^3 (over Qbar).
# Weights (a1,a2,a3; b1,b2,b3; e):
#   H^1(X)   = V1 (x) V2 (x) V3              : (s1,s2,s3; 0,0,0; 0), s in {+-1}^3,
#   H^1(Z_K) = sum_i V_i (x) (D_i + Dbar_i)  : (+-e_i; +-f_i; 0),
#   H^1(E)   = y_iota + y_iotabar            : (0,0,0; 0,0,0; +-1).
# A G-invariant vector of torus character (b; e) is a Hodge class iff b1 = b2 = b3 = d and
# e = -2d (Galois conjugates contain A_3).  SL_2-invariants are counted as
# mult(weight 0) - mult(weight 2) on each factor (inclusion-exclusion over the factors).
# Run: julia --startup-file=no r4_gamma.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms

const W = NTuple{7,Int}
const Z7 = (0, 0, 0, 0, 0, 0, 0)
addw(x, y) = ntuple(i -> x[i] + y[i], 7)
wV() = W[(s1, s2, s3, 0, 0, 0, 0) for s1 in (1, -1) for s2 in (1, -1) for s3 in (1, -1)]
function wD()
    out = W[]
    for i in 1:3, u in (1, -1), v in (1, -1)
        a = zeros(Int, 7); a[i] = u; a[3+i] = v; push!(out, Tuple(a))
    end
    return out
end
wE() = W[(0, 0, 0, 0, 0, 0, 1), (0, 0, 0, 0, 0, 0, -1)]
function wedge(ws, maxdeg)
    poly = Dict(0 => Dict{W,Int}(Z7 => 1))
    for w in ws
        new = Dict(d => copy(m) for (d, m) in poly)
        for (d, m) in poly
            d + 1 > maxdeg && continue
            tgt = get!(new, d + 1, Dict{W,Int}())
            for (k, c) in m; k2 = addw(k, w); tgt[k2] = get(tgt, k2, 0) + c; end
        end
        poly = new
    end
    return poly
end
function tensor(ms...)
    out = Dict{W,Int}(Z7 => 1)
    for m in ms
        new = Dict{W,Int}()
        for (k1, c1) in out, (k2, c2) in m; k = addw(k1, k2); new[k] = get(new, k, 0) + c1 * c2; end
        out = new
    end
    return out
end
deg(p, n) = get(p, n, Dict{W,Int}())
function hodge_dim(m)
    tot = 0
    for d in -12:12, u1 in 0:1, u2 in 0:1, u3 in 0:1
        tot += (-1)^(u1 + u2 + u3) * get(m, (2 * u1, 2 * u2, 2 * u3, d, d, d, -2 * d), 0)
    end
    return tot
end
function ginv_dim(m)                         # dim of G-invariants, all torus characters
    tot = 0
    for u1 in 0:1, u2 in 0:1, u3 in 0:1
        tot += (-1)^(u1 + u2 + u3) * sum((c for (k, c) in m if k[1:3] == (2 * u1, 2 * u2, 2 * u3)); init = 0)
    end
    return tot
end
rep(v, c) = vcat(fill(v, c)...)

function main()
    C = Checks("r4_gamma.jl")
    X = wedge(wV(), 8); Z = wedge(wD(), 12); E1 = wedge(wE(), 2); E2 = wedge(rep(wE(), 2), 4)
    X2Z = wedge(vcat(wV(), wV(), wD()), 4); XZ = wedge(vcat(wV(), wD()), 10)
    check(C, "dim Hdg^4(X^2 x Z) = 26 and dim Hdg^6(X x Z) = 20", hodge_dim(deg(X2Z, 4)) == 26 && hodge_dim(deg(XZ, 6)) == 20)
    check(C, "dim Hom_G(V, H^3(Z)) = 8 (rank of the multiplicity space M)", ginv_dim(tensor(deg(X, 1), deg(Z, 3))) == 8)
    check(C, "no Hodge class in H^1(X) (x) H^3(Z)", hodge_dim(tensor(deg(X, 1), deg(Z, 3))) == 0)
    check(C, "dim Hdg in H^1(X) (x) H^3(Z) (x) H^1(E) (x) H^1(E') = 2 (the k-line of gamma)",
          hodge_dim(tensor(deg(X, 1), deg(Z, 3), deg(E1, 1), deg(E1, 1))) == 2)
    check(C, "dim Hdg in H^1(X) (x) H^3(Z) (x) H^2(E x E') = 2", hodge_dim(tensor(deg(X, 1), deg(Z, 3), deg(E2, 2))) == 2)
    for c in (1, 2, 4)
        XE = wedge(vcat(wV(), rep(wE(), c)), 6); Ec = wedge(rep(wE(), c), 8)
        mixed = [hodge_dim(deg(XE, p)) - sum(hodge_dim(deg(X, i)) * hodge_dim(deg(Ec, p - i)) for i in 0:p) for p in (2, 4, 6)]
        check(C, "X x E^$c: no mixed Hodge classes in degrees 2, 4, 6", all(==(0), mixed))
    end
    for c in 1:4
        Ec = wedge(rep(wE(), c), 2c); ZE = wedge(vcat(wD(), rep(wE(), c)), 12 + 2c)
        row = [hodge_dim(deg(ZE, p)) - sum(hodge_dim(deg(Z, i)) * hodge_dim(deg(Ec, p - i)) for i in 0:p) for p in 0:2:12+2c]
        expect = zeros(Int, length(row)); c == 4 && (expect[6] = 2)
        check(C, "Z x E^$c: mixed Hodge classes by even degree $row" * (c == 4 ? " (two in degree 10: the Weil plane of (Z x E^4, k))" : " (none)"), row == expect)
    end
    finish(C)
end
main()
