# cupkernel.jl -- the cup-product kernel on the diagonal D^2 at n = 4 (Proposition w:prop-efourdiagonal(ii)).
# The 128 line-bundle pieces of E_0^8 are labelled zeta in mu_4^4 with prod zeta = +-1.
# For a type tau (degrees on the four surfaces, |tau| = 2; dimension 2^#{j: tau_j = 1}),
# a component delta of Ext degree q between pieces zeta, zeta' can give a nonzero cup
# product on the tau-part only if tau vanishes on the set S where zeta, zeta' differ,
# and the degrees e_j of delta on the agreeing surfaces satisfy tau_j + e_j <= 2, with
# q = |S| + sum e_j >= 1, q odd iff prod zeta = prod zeta'.  Pieces joined by such a
# potential edge are merged (union-find); each component carries a kernel vector of the
# tau-part, and the 84 diagonal classes of the multiples lie in the kernel.  This gives
# dim ker >= 84 + sum_tau dim(tau) * #components = 484 inside D^2 of dimension 3668.
# Run: julia --startup-file=no cupkernel.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms

const U4 = [(1, 0), (0, 1), (-1, 0), (0, -1)]
gmul(x, y) = (x[1]*y[1] - x[2]*y[2], x[1]*y[2] + x[2]*y[1])
gprod(v) = foldl(gmul, v; init = (1, 0))

function main()
    C = Checks("cupkernel.jl")
    pieces = [collect(z) for z in Iterators.product(U4, U4, U4, U4) if gprod(z) in ((1, 0), (-1, 0))]
    par = [gprod(z) == (1, 0) ? 0 : 1 for z in pieces]
    check(C, "128 pieces zeta in mu_4^4 with prod zeta = +-1", length(pieces) == 128)
    types = [collect(t) for t in Iterators.product(0:2, 0:2, 0:2, 0:2) if sum(t) == 2]
    dimt(t) = 2^count(==(1), t)
    check(C, "10 types tau with |tau| = 2, total dimension 28 per piece (so dim D^2 = 131 * 28 = 3668)",
          length(types) == 10 && sum(dimt, types) == 28 && 131 * 28 == 3668)
    function potential_edge(a, b, t)
        S = [j for j in 1:4 if pieces[a][j] != pieces[b][j]]
        any(t[j] != 0 for j in S) && return false
        agree = [j for j in 1:4 if !(j in S)]
        want_odd = par[a] == par[b]
        for e in Iterators.product([0:(2 - t[j]) for j in agree]...)
            q = length(S) + sum(e; init = 0)
            (q >= 1 && isodd(q) == want_odd) && return true
        end
        return false
    end
    total = 84; comps_by = Int[]
    for t in types
        parent = collect(1:128)
        find(x) = (while parent[x] != x; parent[x] = parent[parent[x]]; x = parent[x]; end; x)
        for a in 1:128, b in a+1:128
            if potential_edge(a, b, t)
                ra, rb = find(a), find(b); ra != rb && (parent[ra] = rb)
            end
        end
        nc = length(Set(find(x) for x in 1:128))
        push!(comps_by, nc)
        total += dimt(t) * nc
    end
    check(C, "components: 4 for the four types tau = 2e_j, 16 for the six types tau = e_j + e_k", 
          all(comps_by[i] == (maximum(types[i]) == 2 ? 4 : 16) for i in 1:10))
    check(C, "cup-product kernel on D^2 has dimension at least 84 + 4*4*1 + 6*16*4 = $total = 484", total == 484)
    finish(C)
end
main()
