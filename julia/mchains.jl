# mchains.jl -- higher Massey chains on a diagonal class at n = 4 (Proposition w:prop-efourdiagonal(iii)).
# A chain: distinct pieces s = a_0 -> ... -> a_K = e (K >= 2 component steps) among
# L (the line-bundle pieces) and the multiples M1, M2, M3, with y inserted at one of them.
# Steps between values: up (Ext degree 0, excess -1), down (Ext degree 8, excess 7);
# L -> L steps have excess lam >= 1.  The term lies in Ext degree 3 + eps,
# eps = sum of excesses, and is nonzero only if: phi(s) < phi(e) and 3 + eps = 0;
# phi(s) > phi(e) and 3 + eps = 8; s, e both L and 1 <= m <= 3 + eps <= 8 - m for
# some m in 1..4.  Two consecutive up-steps a -> b -> c through a multiple b whose
# value is the only one strictly between phi(a) and phi(c) give x_ab x_bc = 0.
# Over the four placements of p among the values, exactly six chain types survive,
# all with four leaves and eps = 5.
# Run: julia --startup-file=no mchains.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms

const MAXLAM = 6
function run(placement)
    ts = [v for v in 0:3 if v != placement]
    vals = Dict("L" => placement, "M1" => ts[1], "M2" => ts[2], "M3" => ts[3])
    surv = Tuple{Vector{String},Vector{Int},Int,Bool}[]
    between(a, c) = (lo = min(vals[a], vals[c]); hi = max(vals[a], vals[c]); [v for v in 0:3 if lo < v < hi])
    function rec(chain, lams)
        K = length(chain) - 1
        if K >= 2 && any(x != "L" for x in chain)
            eps = 0; ups = String[]
            for i in 1:K
                a, b = chain[i], chain[i+1]
                if a == "L" && b == "L"; eps += lams[i]; push!(ups, "LL")
                elseif vals[b] > vals[a]; eps -= 1; push!(ups, "U")
                else; eps += 7; push!(ups, "D"); end
            end
            s, e = chain[1], chain[end]
            ok = if s == "L" && e == "L"
                any(m <= 3 + eps <= 8 - m for m in 1:4)
            elseif vals[s] < vals[e]; 3 + eps == 0
            elseif vals[s] > vals[e]; 3 + eps == 8
            else false end
            if ok
                killed = any(ups[i] == "U" && ups[i+1] == "U" && chain[i+1] != "L" &&
                             between(chain[i], chain[i+2]) == [vals[chain[i+1]]] for i in 1:K-1)
                push!(surv, (copy(chain), copy(lams), eps, killed))
            end
        end
        K >= 9 && return
        peps = 0
        for i in 1:K
            a, b = chain[i], chain[i+1]
            peps += (a == "L" && b == "L") ? lams[i] : (vals[b] > vals[a] ? -1 : 7)
        end
        unused = 3 - count(x -> x != "L", chain)
        peps - (2unused + 1) > 5 && return
        last = chain[end]
        for nxt in ["L", "M1", "M2", "M3"]
            (nxt != "L" && nxt in chain) && continue
            if nxt == "L" && last == "L"
                for lam in 1:MAXLAM; rec(vcat(chain, "L"), vcat(lams, lam)); end
            elseif nxt != last
                rec(vcat(chain, nxt), vcat(lams, 0))
            end
        end
    end
    for start in ["L", "M1", "M2", "M3"]; rec([start], Int[]); end
    return surv
end

function main()
    C = Checks("mchains.jl")
    total = 0; allfour = true; expect = [(5, 1), (5, 2), (5, 2), (5, 1)]
    for pl in 0:3
        surv = run(pl)
        alive = filter(x -> !x[4], surv)
        total += length(alive)
        allfour &= all(length(x[1]) == 4 && x[3] == 5 for x in alive)
        check(C, "p of rank $pl among the values: $(length(surv)) chains pass the degree test, $(length(alive)) survive the Maurer-Cartan filter: $(join([join(x[1], "->") for x in alive], ", "))",
              (length(surv), length(alive)) == expect[pl+1])
    end
    check(C, "exactly 6 surviving chain types, each with four leaves (three multiples and L) and eps = 5", total == 6 && allfour)
    finish(C)
end
main()
