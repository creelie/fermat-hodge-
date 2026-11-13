# link_invariants.jl -- the counts behind Theorems thm:linkall, thm:tenfold
# and Proposition prop:zkpowers: dimensions of the Hodge classes on
# X^a x Z_K^b at a very general point of the Shimura curve, where the Hodge
# group is G.K^1, over Qbar SL_2^3 x G_m^3 (up to a finite group), acting on
#   H^1(X)   = V = V1 (x) V2 (x) V3,            weights (s1,s2,s3; 0,0,0),
#   H^1(Z_K) = D = sum_i V_i (x) (chi_i + chi_i^-1), weights (+-e_i; +-f_i).
# Invariants of SL_2^3 x G_m^3 in a module with weight multiplicities m are
# sum_{eps in {0,1}^3} (-1)^|eps| m(2 eps; 0).  Exact integer counts.
# Run: julia --startup-file=no link_invariants.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms: Checks, check, finish
using LinearAlgebra

const W6 = NTuple{6,Int}
weightsV() = [(s1, s2, s3, 0, 0, 0) for s1 in (1, -1) for s2 in (1, -1) for s3 in (1, -1)]
function weightsD()
    w = W6[]
    for i in 1:3, u in (1, -1), v in (1, -1)
        a = zeros(Int, 6); a[i] = u; a[3+i] = v; push!(w, Tuple(a))
    end
    return w
end
addw(a, b) = ntuple(i -> a[i] + b[i], 6)
function wedge_poly(ws, maxdeg)
    poly = Dict(0 => Dict{W6,Int}(ntuple(_ -> 0, 6) => 1))
    for w in ws
        new = Dict(d => copy(m) for (d, m) in poly)
        for (d, m) in poly
            d + 1 > maxdeg && continue
            tgt = get!(new, d + 1, Dict{W6,Int}())
            for (k, c) in m
                k2 = addw(k, w); tgt[k2] = get(tgt, k2, 0) + c
            end
        end
        poly = new
    end
    return poly
end
function hwmult(m, hw)
    tot = 0
    for e1 in 0:1, e2 in 0:1, e3 in 0:1
        tot += (-1)^(e1 + e2 + e3) * get(m, (hw[1] + 2 * e1, hw[2] + 2 * e2, hw[3] + 2 * e3, 0, 0, 0), 0)
    end
    return tot
end
inv_dim(m) = hwmult(m, (0, 0, 0))
function tensor(m1, m2)
    out = Dict{W6,Int}()
    for (k1, c1) in m1, (k2, c2) in m2
        k = addw(k1, k2); out[k] = get(out, k, 0) + c1 * c2
    end
    return out
end
getp(P, d) = get(P, d, Dict{W6,Int}())

"rows (p, dim B^p(X^a x Z^b), dim [B(X^a) (x) B(Z^b)]^p)"
function table(a, b, maxdeg)
    PX = wedge_poly(repeat(weightsV(), a), maxdeg); PZ = wedge_poly(repeat(weightsD(), b), maxdeg)
    invX = [inv_dim(getp(PX, d)) for d in 0:maxdeg]; invZ = [inv_dim(getp(PZ, d)) for d in 0:maxdeg]
    rows = Tuple{Int,Int,Int}[]
    for p in 0:2:maxdeg
        tot = sum(inv_dim(tensor(getp(PX, i), getp(PZ, p - i))) for i in 0:p)
        prd = sum(invX[i+1] * invZ[p-i+1] for i in 0:p)
        push!(rows, (p, tot, prd))
    end
    return invX, invZ, rows
end

function main()
    C = Checks("link_invariants.jl")
    PV = wedge_poly(weightsV(), 8); PD = wedge_poly(weightsD(), 12)
    bX = [inv_dim(getp(PV, d)) for d in 0:8]; bZ = [inv_dim(getp(PD, d)) for d in 0:12]
    check(C, "dim B^p(X), p = 0..8: 1,0,1,0,1,0,1,0,1", bX == [1, 0, 1, 0, 1, 0, 1, 0, 1])
    check(C, "dim B^p(Z_K), p = 0..12: 1,0,3,0,6,0,7,0,6,0,3,0,1 (Prop. prop:zkpowers)", bZ == [1, 0, 3, 0, 6, 0, 7, 0, 6, 0, 3, 0, 1])
    _, iZ2, rZ2 = table(0, 2, 8)
    check(C, "dim B^p(Z_K^2), p = 0,2,4,6,8: 1,12,78,316,879, all in the divisor algebra", [r[2] for r in rZ2] == [1, 12, 78, 316, 879] && all(r[2] == r[3] for r in rZ2))
    _, _, rX2 = table(2, 0, 8)
    check(C, "dim B^p(X^2), p = 0..8 even: 1,3,8,16,28", [r[2] for r in rX2] == [1, 3, 8, 16, 28])
    want = Dict((1, 1) => [(0, 1, 1), (2, 4, 4), (4, 10, 10), (6, 20, 17), (8, 29, 23), (10, 35, 25)],
                (2, 1) => [(0, 1, 1), (2, 6, 6), (4, 26, 23), (6, 98, 65), (8, 293, 151)],
                (2, 2) => [(0, 1, 1), (2, 15, 15), (4, 134, 122), (6, 995, 662)])
    for (ab, md) in (((1, 1), 10), ((2, 1), 8), ((2, 2), 6))
        _, _, rows = table(ab[1], ab[2], md)
        check(C, "X^$(ab[1]) x Z^$(ab[2]): (p, dim B^p, dim of the product algebra) = $(want[ab])", rows == want[ab])
    end
    # Kuenneth components on X x Z_K
    comp(i, j) = inv_dim(tensor(getp(PV, i), getp(PD, j)))
    check(C, "X x Z_K, degree 6: components (2,4) 9 = 6 + 3, (0,6) 7, (4,2) 3, (6,0) 1; degree 4 has no mixed class",
          comp(2, 4) == 9 && bX[3] * bZ[5] == 6 && comp(0, 6) == 7 && comp(4, 2) == 3 && comp(6, 0) == 1 &&
          comp(0, 4) == 6 && comp(2, 2) == 3 && comp(4, 0) == 1)
    tot4 = 0; c112 = 0
    for i in 0:4, j in 0:4-i
        n = inv_dim(tensor(tensor(getp(PV, i), getp(PV, j)), getp(PD, 4 - i - j)))
        tot4 += n; (i, j) == (1, 1) && (c112 = n)
    end
    check(C, "X x X x Z_K, degree 4: total 26, component (1,1,2) of dimension 6 = 3 + 3", tot4 == 26 && c112 == 6)
    check(C, "multiplicity 1 of T_1 = S^2 V_1 in (wedge^2 D)^{K^1} and in V (x) V; 0 in wedge^2 V and wedge^4 V",
          hwmult(getp(PD, 2), (2, 0, 0)) == 1 && hwmult(tensor(getp(PV, 1), getp(PV, 1)), (2, 0, 0)) == 1 &&
          hwmult(getp(PV, 2), (2, 0, 0)) == 0 && hwmult(getp(PV, 4), (2, 0, 0)) == 0)
    check(C, "multiplicity 1 of U_3 = S^2V_1 (x) S^2V_2 in (wedge^4 D)^{K^1} and in wedge^2 V",
          hwmult(getp(PD, 4), (2, 2, 0)) == 1 && hwmult(getp(PV, 2), (2, 2, 0)) == 1)
    # the action of b in F on U_Z is N(b)^2 b^-2; these elements span F over Q (cubic fields of
    # discriminant 49, 81, 148): multiplication matrices in Q[t]/(f)
    for f in ([-1, -2, 1, 1], [1, -3, 0, 1], [1, -3, -1, 1])           # t^3 + t^2 - 2t - 1, t^3 - 3t + 1, t^3 - t^2 - 3t + 1
        Mt = Rational{BigInt}[0 0 -f[1]; 1 0 -f[2]; 0 1 -f[3]]
        mulm(c) = c[1] * Matrix{Rational{BigInt}}(I, 3, 3) + c[2] * Mt + c[3] * Mt^2
        vecs = Vector{Rational{BigInt}}[]
        for b in ([1, 1, 0], [2, 1, 0], [0, 1, 1])
            Mb = mulm(b); y = det(Mb)^2 * inv(Mb)^2
            push!(vecs, y[:, 1])                                       # coordinates of N(b)^2 b^-2
        end
        okspan = rank(Float64.(hcat([1, 0, 0], vecs[1], vecs[2]))) == 3 && det(hcat(Rational{BigInt}[1, 0, 0], vecs[1], vecs[2])) != 0
        okirr = all(y -> !(y[2] == 0 && y[3] == 0), vecs)
        check(C, "F = Q[t]/($(f)): the elements N(b)^2 b^-2, b = 1+t, 2+t, t+t^2, are irrational and with 1 span F", okspan && okirr)
    end
    finish(C)
end
main()
