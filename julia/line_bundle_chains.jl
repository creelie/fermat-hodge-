# Line bundles in any number at the CM point A_0 = E_0^6 (Theorem VI.23 and Remark VI.25).
# Julia port of code/line_bundle_chains.py; same graph, same rules, same counts.
#
# A configuration is a tuple of shifts of n line bundles, the i-th entry being the shift of the line
# bundle of i-th smallest exponent.  Edges of the abstract graph between line bundles:
#   up    L^l[s] -> L^l'[s+1], l' > l           (Hom, degree 0)
#   down  L^l[s] -> L^l'[s-5], l' < l           (Ext^6)
#   run   L^l[s] -> threefold pieces -> L^l'[s-b], b >= 1 (degrees of Lemmas VI.8 and VI.9).
# Over every set Z0 of up edges on which delta vanishes: rule E2 (Lemma VI.20(i)) rejects Z0 when
# for two line bundles two shifts apart a -> b -> c is the only path avoiding Z0; rule E3 (Lemma
# VI.20(ii)) kills a cycle whose zero edge lies on an a -> b -> c that is the only path of the graph
# with exactly one of its two edges in Z0; a cycle through a run is effective when it has at most one
# edge in Z0, not killed.  An arrangement is 'both' when for one Z0 the effective cycles pass through
# threefold pieces of both parities of shift.
#
#   julia --startup-file=no line_bundle_chains.jl [NMAX]     (NMAX = 8 by default, at most 8)
#
# Exact integer arithmetic only; no packages.

module LineBundleChains

export BMAX, RUNS, graph, paths, cycles, classify, contiguous_each, coarse_data, PathInfo

const BMAX = 12   # largest excess of a run that can matter

# ---------------------------------------------------------------- the degrees of Lemmas VI.8, VI.9
# relations are coded 1: '<', 2: '=', 3: '>'
const LT, EQ, GT = 1, 2, 3
enter_degrees(rel) = rel == GT ? (0,) : rel == LT ? (3,) : (0, 1, 2, 3)     # Ext^*(L^l, O_Z L^k), rel = k ? l
leave_degrees(rel) = rel == LT ? (3,) : rel == GT ? (6,) : (3, 4, 5, 6)     # Ext^*(O_Z L^k, L^l), rel = k ? l
# Ext^*(O_Z L^k, O_Z' L^k') for Z != Z': directions 1 up, 2 eq, 3 down
internal_degrees(dir) = dir == 1 ? (2, 3) : dir == 2 ? (2, 3, 4, 5) : (3, 4, 5)

# relation to l' after a step
function step_rel(rel, dir)
    if dir == 1
        return rel == LT ? (LT, EQ, GT) : (GT,)
    elseif dir == 2
        return (rel,)
    else
        return rel == GT ? (LT, EQ, GT) : (LT,)
    end
end

const FINISH = Dict{Tuple{Int,Int},Set{Int}}()
"total excesses reachable from a threefold at accumulated excess x, relation rel to l'"
function finish(rel::Int, x::Int)
    key = (rel, x)
    haskey(FINISH, key) && return FINISH[key]
    tot = Set{Int}(x + d - 1 for d in leave_degrees(rel))
    if x < BMAX
        for dir in 1:3, d in internal_degrees(dir)
            if x + d - 1 <= BMAX
                for rel2 in step_rel(rel, dir)
                    union!(tot, finish(rel2, x + d - 1))
                end
            end
        end
    end
    res = Set{Int}(t for t in tot if t <= BMAX)
    FINISH[key] = res
    return res
end

"RUNS[(b, dec)]: the excesses accumulated before a threefold piece, over all runs of total excess b
from L^l to L^l' with l' < l (dec) or l' > l (not dec)."
function run_table()
    table = Dict{Tuple{Int,Bool},Vector{Int}}()
    for dec in (false, true)
        # relation of k_1 to l' from the relation of k_1 to l
        first(rel) = dec ? (rel == LT ? (LT, EQ, GT) : (GT,)) : (rel == GT ? (LT, EQ, GT) : (LT,))
        seen = Set{Tuple{Int,Int}}()
        stack = Tuple{Int,Int}[]
        for rel_l in (LT, EQ, GT), d in enter_degrees(rel_l), rel in first(rel_l)
            st = (rel, d - 1)
            if !(st in seen)
                push!(seen, st); push!(stack, st)
            end
        end
        while !isempty(stack)
            rel, x = pop!(stack)
            x >= BMAX && continue
            for dir in 1:3, d in internal_degrees(dir), rel2 in step_rel(rel, dir)
                st = (rel2, x + d - 1)
                if st[2] <= BMAX && !(st in seen)
                    push!(seen, st); push!(stack, st)
                end
            end
        end
        for b in 1:BMAX
            table[(b, dec)] = sort!(unique!([x for (rel, x) in seen if b in finish(rel, x)]))
        end
    end
    return table
end

const RUNS = run_table()

# ---------------------------------------------------------------- the graph on a configuration
# an adjacency entry: (target, kind, data); kind 1 up (data = up-edge index, from 0), 2 run (data =
# bit mask of the parities of the threefold shifts, bit p for parity p), 3 down (data = 0).
const Adj = Vector{Vector{Tuple{Int,Int,Int}}}

function graph(s)
    n = length(s)
    up = Tuple{Int,Int}[]
    adj = [Tuple{Int,Int,Int}[] for _ in 1:n]
    for a in 1:n, b in a+1:n
        if s[b] == s[a] + 1
            push!(up, (a, b))
            push!(adj[a], (b, 1, length(up) - 1))
        end
    end
    for a in 1:n, b in 1:n
        b == a && continue
        beta = s[a] - s[b]
        if beta >= 1
            xs = get(RUNS, (beta, b < a), Int[])
            if !isempty(xs)
                par = 0
                for x in xs
                    par |= 1 << mod(s[a] - x, 2)
                end
                push!(adj[a], (b, 2, par))
            end
        end
        if b < a && s[b] == s[a] - 5
            push!(adj[a], (b, 3, 0))
        end
    end
    return up, adj
end

"a path between two line bundles: mask of its up edges, number of edges, whether it has a run or a down edge"
struct PathInfo
    ups::UInt64
    len::Int
    other::Bool
end
twoup(p::PathInfo) = p.len == 2 && !p.other

function paths!(out::Vector{PathInfo}, adj::Adj, v::Int, c::Int, vis::UInt64, ups::UInt64, len::Int, other::Bool)
    for (w, kind, data) in adj[v]
        (vis >> w) & 1 == 1 && continue
        nups = kind == 1 ? ups | (UInt64(1) << data) : ups
        noth = other || kind != 1
        if w == c
            push!(out, PathInfo(nups, len + 1, noth))
        else
            paths!(out, adj, w, c, vis | (UInt64(1) << w), nups, len + 1, noth)
        end
    end
    return out
end
"all paths a -> c through distinct line bundles"
paths(adj::Adj, a::Int, c::Int) = paths!(PathInfo[], adj, a, c, UInt64(1) << a, UInt64(0), 0, false)

function cycles!(out::Vector{Tuple{UInt64,Int}}, adj::Adj, start::Int, v::Int, vis::UInt64, ups::UInt64, par::Int, hasrun::Bool)
    for (w, kind, data) in adj[v]
        nups, npar, nrun = ups, par, hasrun
        if kind == 1
            nups |= UInt64(1) << data
        elseif kind == 2
            npar |= data; nrun = true
        end
        if w == start
            nrun && push!(out, (nups, npar))
            continue
        end
        (w < start || (vis >> w) & 1 == 1) && continue
        cycles!(out, adj, start, w, vis | (UInt64(1) << w), nups, npar, nrun)
    end
    return out
end
"directed cycles through at least one run, as (mask of up edges, mask of parities)"
function cycles(adj::Adj, n::Int)
    out = Tuple{UInt64,Int}[]
    for start in 1:n
        cycles!(out, adj, start, start, UInt64(1) << start, UInt64(0), 0, false)
    end
    return out
end

"up edges, cycles and, for every pair of line bundles two shifts apart, all the paths between them"
function coarse_data(s)
    n = length(s)
    up, adj = graph(s)
    cyc = cycles(adj, n)
    prs = Vector{PathInfo}[]
    for a in 1:n, c in a+1:n
        s[c] == s[a] + 2 || continue
        push!(prs, paths(adj, a, c))
    end
    return up, adj, cyc, prs
end

"rule E2: is the dead set z0 rejected?"
function e2_bad(prs, z0::UInt64)
    for ps in prs
        cnt = 0; two = false
        for p in ps
            if p.ups & z0 == 0
                cnt += 1; two = twoup(p)
                cnt > 1 && break
            end
        end
        cnt == 1 && two && return true
    end
    return false
end

"rule E3 of the paper: up edges on which eta vanishes"
function e3_dead(prs, z0::UInt64)
    dead = UInt64(0)
    for ps in prs
        if length(ps) == 1 && twoup(ps[1])
            m = ps[1].ups & z0
            count_ones(m) == 1 && (dead |= m)
        end
    end
    return dead
end

"rule E3*: the same when every other path carries at least two dead up edges"
function e3star_dead(prs, z0::UInt64)
    dead = UInt64(0)
    for ps in prs
        cnt = 0; m = UInt64(0); two = false
        for p in ps
            if count_ones(p.ups & z0) <= 1
                cnt += 1; m = p.ups & z0; two = twoup(p)
                cnt > 1 && break
            end
        end
        if cnt == 1 && two && count_ones(m) == 1
            dead |= m
        end
    end
    return dead
end

"parities reached by the effective cycles for the dead set z0 and the forced set dead"
function reach_par(cyc, z0::UInt64, dead::UInt64)
    r = 0
    for (ups, par) in cyc
        zs = ups & z0
        if count_ones(zs) <= 1 && zs & dead == 0
            r |= par
        end
    end
    return r
end

"2 ('both'), 1 ('one') or 0 ('none'); refined = true uses rule E3* in place of rule E3"
function classify(s; refined::Bool=false)
    up, adj, cyc, prs = coarse_data(s)
    isempty(cyc) && return 0
    best = 0
    for z in 0:(1<<length(up))-1
        z0 = UInt64(z)
        e2_bad(prs, z0) && continue
        dead = refined ? e3star_dead(prs, z0) : e3_dead(prs, z0)
        r = reach_par(cyc, z0, dead)
        r == 3 && return 2
        best |= r
    end
    return best != 0 ? 1 : 0
end

"calls f on every configuration of n shifts whose set of shifts is an interval {0, ..., k-1} (Lemma VI.24)"
function contiguous_each(f, n::Int)
    conf = zeros(Int, n)
    cnt = zeros(Int, n)
    for k in 1:n
        fill!(conf, 0); fill!(cnt, 0); cnt[1] = n
        distinct = 1
        while true
            distinct == k && f(conf)
            i = n                     # odometer, last entry fastest (the order of itertools.product)
            while i >= 1 && conf[i] == k - 1
                cnt[k] -= 1; cnt[k] == 0 && (distinct -= 1)
                conf[i] = 0
                cnt[1] += 1; cnt[1] == 1 && (distinct += 1)
                i -= 1
            end
            i == 0 && break
            v = conf[i]
            cnt[v+1] -= 1; cnt[v+1] == 0 && (distinct -= 1)
            conf[i] = v + 1
            cnt[v+2] += 1; cnt[v+2] == 1 && (distinct += 1)
        end
    end
end

const EXPECTED = Dict(      # n => (configurations, both parities, one parity, none)
    4 => (75, 0, 0, 75),
    5 => (541, 0, 0, 541),
    6 => (4683, 0, 4, 4679),
    7 => (47293, 0, 140, 47153),
    8 => (545835, 31, 3235, 542569),
)

rank_of(conf) = sum(isodd(t) ? -1 : 1 for t in conf)

function main(args)
    nmax = isempty(args) ? 8 : min(8, parse(Int, args[1]))
    npass = 0; nfail = 0
    function check(name, ok)
        println(ok ? "PASS " : "FAIL ", name)
        ok ? (npass += 1) : (nfail += 1)
    end
    for b in 1:7
        println("  run excess $b: threefolds at excess $(RUNS[(b, false)]) (exit above), $(RUNS[(b, true)]) (exit below)")
    end
    both8 = Vector{Int}[]
    for n in 4:nmax
        total = 0; one = 0; none = 0
        both = Vector{Int}[]
        contiguous_each(n) do conf
            total += 1
            c = classify(conf)
            if c == 2
                push!(both, copy(conf))
            elseif c == 1
                one += 1
            else
                none += 1
            end
        end
        sort!(both)
        got = (total, length(both), one, none)
        check("$n line bundles: $(got[1]) configurations, $(got[2]) carry both parities, $(got[3]) one, $(got[4]) none" *
              (got == EXPECTED[n] ? "" : "  (expected $(EXPECTED[n]))"), got == EXPECTED[n])
        for conf in both
            println("      both: (", join(conf, ", "), ")   rank ", rank_of(conf))
        end
        n == 8 && (both8 = both)
    end
    if nmax >= 8
        r0 = count(c -> rank_of(c) == 0, both8)
        r2 = count(c -> abs(rank_of(c)) == 2, both8)
        check("ranks sum (-1)^t of the thirty-one arrangements of eight: $r0 of rank 0, $r2 of rank +-2", r0 == 23 && r2 == 8)
    end
    println("line_bundle_chains.jl: $npass checks passed, $nfail failed")
    return nfail
end

end # module

if abspath(PROGRAM_FILE) == @__FILE__
    exit(LineBundleChains.main(ARGS) > 0 ? 1 : 0)
end
