# Theorem w:thm-lagrangian: the cost inequality is sharp at the level of windows.
# Abstract configurations of proper pieces P(lambda) (an n-dimensional abelian translate with a semihomogeneous bundle
# whose slope has relative eigenvalues lambda_1 <= ... <= lambda_n) with pairwise transverse supports, and l bundles
# M_t of slope t theta with distinct t.  Ext windows (Lemmas w:lem-windows, w:lem-lagrangian):
#   P -> P': [n, n];  M_t -> P: [#{lambda < t}, n - #{lambda > t}];  P -> M_t: n + [#{lambda > t}, n - #{lambda < t}];
#   M_t -> M_s: [0, 0] if s > t, [2n, 2n] if s < t.
# For each l and with or without P -> P' edges, the least cost sum(lower - 1) of a directed cycle of distinct pieces
# through a proper piece, over all configurations with values 0..V: n = 3 (V = 6, at most two proper pieces) and
# n = 4 (V = 7, one proper piece).  Claims: the cost is positive exactly for l <= 2n - 3 (with P -> P' edges, two
# proper pieces) and for l <= 2n - 2 (without them, or with one proper piece); at the thresholds cycles of cost 0 exist.
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms

struct Piece; isP::Bool; lam::Vector{Int}; t::Int; end
function windows(n, pieces, pp)
    V = length(pieces); E = Dict{Tuple{Int,Int},Tuple{Int,Int}}()
    for i in 1:V, j in 1:V
        i == j && continue
        a, b = pieces[i], pieces[j]
        if a.isP && b.isP
            pp && (E[(i, j)] = (n, n))
        elseif !a.isP && b.isP
            E[(i, j)] = (count(<(a.t), b.lam), n - count(>(a.t), b.lam))
        elseif a.isP && !b.isP
            E[(i, j)] = (n + count(>(b.t), a.lam), 2n - count(<(b.t), a.lam))
        else
            b.t > a.t ? (E[(i, j)] = (0, 0)) : (E[(i, j)] = (2n, 2n))
        end
    end
    E
end
function min_cycle(n, pieces, pp)
    E = windows(n, pieces, pp); V = length(pieces)
    out = [[(j, E[(i, j)][1]) for j in 1:V if haskey(E, (i, j))] for i in 1:V]
    best = typemax(Int); visited = falses(V)
    function dfs(start, v, nvis, lo)
        rem = V - nvis
        best != typemax(Int) && lo - (rem + 1) >= best && return
        for (w, l) in out[v]
            if w == start
                best = min(best, lo + l - 1)
            elseif !visited[w] && !(pieces[w].isP && w < start)
                visited[w] = true; dfs(start, w, nvis + 1, lo + l - 1); visited[w] = false
            end
        end
    end
    for s in 1:V
        pieces[s].isP || continue
        visited[s] = true; dfs(s, s, 1, 0); visited[s] = false
    end
    best
end
mcombs(vals, k) = k == 0 ? [Int[]] : [vcat(s, [x]) for s in mcombs(vals, k - 1) for x in vals if isempty(s) || x >= s[end]]
combs(vals, k) = k == 0 ? [Int[]] : [vcat(s, [x]) for s in combs(vals, k - 1) for x in vals if isempty(s) || x > s[end]]

C = Checks("window_search.jl")
for (n, V, maxprop) in ((3, 6, 2), (4, 7, 1))
    vals = collect(0:V); lamsets = mcombs(vals, n)
    mins = Dict{Tuple{Int,Bool},Int}()
    for ell in 0:2n-1, pp in (true, false)
        mn = typemax(Int)
        for ts in combs(vals, ell), npr in 1:maxprop
            for choice in mcombs(collect(1:length(lamsets)), npr)
                pieces = vcat([Piece(true, lamsets[c], 0) for c in choice], [Piece(false, Int[], t) for t in ts])
                mn = min(mn, min_cycle(n, pieces, pp))
            end
        end
        mins[(ell, pp)] = mn
    end
    for pp in (true, false)
        thr = (pp && maxprop >= 2) ? 2n - 3 : 2n - 2
        pos = [ell for ell in 0:2n-1 if mins[(ell, pp)] > 0]
        costs = [mins[(ell, pp)] == typemax(Int) ? "none" : string(mins[(ell, pp)]) for ell in 0:2n-1]
        check(C, "n=$n, $(pp ? "with" : "without") P->P' edges: least cost for l = 0..$(2n-1) is $(join(costs, ",")); positive exactly for l <= $thr, 0 at l = $(thr+1)",
              pos == collect(0:thr) && mins[(thr + 1, pp)] == 0)
    end
end
finish(C)
