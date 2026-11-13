# twolevel.jl -- the two-level equivariant count on E_0^8 (Theorem w:thm-equivtwoshift).
# Pieces zeta in mu_4^4 with prod zeta = +-1; types tau with |tau| = 2 as in cupkernel.jl.
# In a two-level arrangement a potential cup-product edge of type tau joins pieces of
# opposite parity with tau = 0 on the difference set S, where |S| = 1 needs an agreeing
# surface k with tau_k <= 1 and |S| = 2 is always allowed (|S| >= 3: H^2 vanishes).
# Each edge is labelled by the slices (k, zeta_k), k agreeing, through which it passes,
# and survives only if all these slices are nonconstant.  For every set Sigma of N <= 5
# nonconstant slices (6885 sets) the cup-kernel bound 84 + sum dim(tau) * #components is
# minimised; the diagonal contributes max(0, bound - (84 + 28 * 64)) and every
# nonconstant slice contributes at least its minimum cut 20 (slices.jl).  Minima:
# N = 0..5: 1792, 1812, 1796, 1729, 1632, 1535; N >= 6 gives >= 120.
# Run: julia --startup-file=no twolevel.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms

const U4 = [(1, 0), (0, 1), (-1, 0), (0, -1)]
gmul(x, y) = (x[1]*y[1] - x[2]*y[2], x[1]*y[2] + x[2]*y[1])
gprod(v) = foldl(gmul, v; init = (1, 0))

function combos(n, k)               # all k-subsets of 1:n
    out = Vector{Int}[]; c = collect(1:k)
    k == 0 && return [Int[]]
    while true
        push!(out, copy(c))
        i = k
        while i >= 1 && c[i] == n - k + i; i -= 1; end
        i == 0 && return out
        c[i] += 1
        for j in i+1:k; c[j] = c[j-1] + 1; end
    end
end

function main()
    C = Checks("twolevel.jl")
    pieces = [collect(z) for z in Iterators.product(U4, U4, U4, U4) if gprod(z) in ((1, 0), (-1, 0))]
    par = [gprod(z) == (1, 0) ? 0 : 1 for z in pieces]
    slices = [(j, z) for j in 1:4 for z in U4]
    sidx = Dict(s => i for (i, s) in enumerate(slices))
    types = [(collect(t), 2^count(==(1), t)) for t in Iterators.product(0:2, 0:2, 0:2, 0:2) if sum(t) == 2]
    TE = []
    for (t, d) in types
        E = Tuple{Int,Int,UInt16}[]
        for a in 1:128, b in a+1:128
            par[a] == par[b] && continue
            S = [j for j in 1:4 if pieces[a][j] != pieces[b][j]]
            any(t[j] > 0 for j in S) && continue
            agree = [j for j in 1:4 if !(j in S)]
            if length(S) == 1
                any(t[k] <= 1 for k in agree) || continue
            elseif length(S) != 2
                continue
            end
            mask = UInt16(0)
            for k in agree; mask |= UInt16(1) << (sidx[(k, pieces[a][k])] - 1); end
            push!(E, (a, b, mask))
        end
        push!(TE, (d, E))
    end
    parent = zeros(Int, 128)
    function ncomp(E, allowed::UInt16)
        for x in 1:128; parent[x] = x; end
        find(x) = (while parent[x] != x; parent[x] = parent[parent[x]]; x = parent[x]; end; x)
        for (a, b, m) in E
            if m & ~allowed == 0
                ra, rb = find(a), find(b); ra != rb && (parent[ra] = rb)
            end
        end
        return count(x -> parent[x] == x, 1:128)
    end
    full = ~UInt16(0)
    check(C, "cup-kernel bound with all two-level edges allowed = 484", 84 + sum(d * ncomp(E, full) for (d, E) in TE) == 484)
    expect = [1792, 1812, 1796, 1729, 1632, 1535]; got = Int[]; nsets = 0
    for N in 0:5
        mn = typemax(Int)
        for sub in combos(16, N)
            nsets += 1
            allowed = UInt16(0); for s in sub; allowed |= UInt16(1) << (s - 1); end
            mn = min(mn, 84 + sum(d * ncomp(E, allowed) for (d, E) in TE))
        end
        push!(got, 20N + max(0, mn - (84 + 28 * 64)))
    end
    check(C, "$nsets sets of N <= 5 nonconstant slices; minimal totals 20N + diagonal bound for N = 0..5: $got", got == expect && nsets == 6885)
    check(C, "minimum over all N (N >= 6 contributes >= 20 * 6 = 120): $(min(minimum(got), 120)) = 120", min(minimum(got), 120) == 120)
    finish(C)
end
main()
