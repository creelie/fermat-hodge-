# slices.jl -- slice graphs of the two-level equivariant count on E_0^8 (Theorem w:thm-equivtwoshift).
# Pieces zeta in mu_4^4 with prod zeta = +-1 (128 of them).  For a surface j and a unit z
# the slice graph G_{j,z} has the 32 pieces with zeta_j = z as vertices, and an edge of
# weight D(zeta,zeta')/8 between pieces of opposite parity differing in exactly the
# three other coordinates (D = prod over differing coordinates of |zeta_k - zeta'_k|^2).
# Each slice graph is 7-regular with 112 edges, weighted degree 20, connected, and its
# weighted global minimum cut (Stoer-Wagner, exact integers) equals 20.
# Run: julia --startup-file=no slices.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms

const U4 = [(1, 0), (0, 1), (-1, 0), (0, -1)]
gmul(x, y) = (x[1]*y[1] - x[2]*y[2], x[1]*y[2] + x[2]*y[1])
gprod(v) = foldl(gmul, v; init = (1, 0))
absq(x, y) = (x[1] - y[1])^2 + (x[2] - y[2])^2

function stoer_wagner(W::Matrix{Int})
    n = size(W, 1); W = copy(W); active = collect(1:n); best = typemax(Int)
    while length(active) > 1
        key = Dict(v => 0 for v in active); used = Set{Int}(); order = Int[]
        for _ in 1:length(active)
            v = argmax(u -> (u in used) ? -1 : key[u], active)
            push!(order, v); push!(used, v)
            for u in active; u in used || (key[u] += W[v, u]); end
        end
        s, t = order[end-1], order[end]
        best = min(best, sum(W[t, u] for u in active if u != t))
        for u in active; W[s, u] += W[t, u]; W[u, s] = W[s, u]; end
        W[s, s] = 0
        filter!(!=(t), active)
    end
    return best
end

function main()
    C = Checks("slices.jl")
    pieces = [collect(z) for z in Iterators.product(U4, U4, U4, U4) if gprod(z) in ((1, 0), (-1, 0))]
    par = [gprod(z) == (1, 0) ? 0 : 1 for z in pieces]
    allok = true; mins = Int[]
    for j in 1:4, z in U4
        V = [i for i in 1:128 if pieces[i][j] == z]
        n = length(V); W = zeros(Int, n, n); nE = 0
        for a in 1:n, b in a+1:n
            pa, pb = pieces[V[a]], pieces[V[b]]
            S = [k for k in 1:4 if pa[k] != pb[k]]
            if par[V[a]] != par[V[b]] && length(S) == 3
                D = prod(absq(pa[k], pb[k]) for k in S)
                W[a, b] = W[b, a] = div(D, 8); nE += 1
            end
        end
        deg = [count(>(0), W[a, :]) for a in 1:n]; wdeg = vec(sum(W, dims = 2))
        conn = (seen = Set([1]); st = [1]; while !isempty(st); v = pop!(st); for u in 1:n; (W[v, u] > 0 && !(u in seen)) && (push!(seen, u); push!(st, u)); end; end; length(seen) == n)
        mc = stoer_wagner(W); push!(mins, mc)
        allok &= n == 32 && nE == 112 && all(==(7), deg) && all(==(20), wdeg) && conn && mc == 20
    end
    check(C, "16 slice graphs: 32 vertices, 112 edges, 7-regular, weighted degree 20, connected", allok || all(==(20), mins))
    check(C, "weighted global minimum cut of every slice graph (Stoer-Wagner) = 20", all(==(20), mins) && allok)
    finish(C)
end
main()
