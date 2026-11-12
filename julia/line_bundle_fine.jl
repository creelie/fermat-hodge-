# Finer necessary conditions on the arrangements of line bundles at E_0^6 left open by the enumeration
# of line_bundle_chains.jl.  Julia port of the round programs chains_refined.py, fine_model.py,
# fine_check.py, fine9.py and chains9.py.
#
# Section 1 (chains_refined.py).  The enumeration of line_bundle_chains.jl with rule E3 replaced by
#   E3*  Let a -> b -> c be two up edges, exactly one of which is dead (delta = 0) for the dead set Z0.
#        If every other path of the graph from a to c carries at least two dead up edges, then eta
#        vanishes on the dead edge of a -> b -> c.
# Section 2 (fine_model.py).  The support of delta is a variable: a state is a set G of live abstract
# edges (up, down, run pair).  Necessary conditions:
#   C1  G has no directed cycle;
#   C2  rule E2: for a, c two shifts apart, a -> b -> c is not the only G-path from a to c;
#   C4  rule E3* iterated: for a, c two shifts apart with no G-path from a to c, if among the abstract
#       paths from a to c with exactly one edge e outside G, eta_e not already known to vanish, there
#       is exactly one and it is a -> b -> c, then eta_e = 0;
#   C3  for each parity there is an abstract cycle through a run admitting threefold shifts of that
#       parity with exactly one edge e outside G, eta_e not forced to vanish.
# All 2^m states of each of the thirty-one arrangements of eight are enumerated.
# Section 3 (fine_check.py).  The same count by a second implementation that shares only the run table
# (edge lists and paths as lists of edge indices, no bit masks, another order of the edges).
# Section 4 (fine9.py 8).  The count restricted to the states whose dead up edges form a witness of
# the coarse enumeration of Section 1.
# Section 5 (chains9.py, fine9.py chains9.out).  Nine line bundles.
#
#   julia --startup-file=no line_bundle_fine.jl            (all sections)
#   julia --startup-file=no line_bundle_fine.jl --no-nine  (Sections 1 to 4 only)
#
# Exact integer arithmetic only; no packages.

include(joinpath(@__DIR__, "line_bundle_chains.jl"))

module LineBundleFine

using ..LineBundleChains
const L = LineBundleChains

const C31 = [[0,0,1,2,1,2,2,3],[0,0,1,2,1,2,3,3],[0,1,0,1,2,3,3,4],[0,1,1,2,1,2,2,3],[0,1,1,2,1,2,3,3],[0,1,1,2,1,2,3,4],
             [0,1,1,2,2,3,3,4],[0,1,1,2,2,3,4,3],[0,1,1,2,3,2,3,4],[0,1,1,2,3,4,3,4],[0,1,2,1,2,2,3,4],[0,1,2,1,2,3,3,4],
             [0,1,2,1,2,3,4,3],[0,1,2,1,3,2,3,4],[0,1,2,2,1,2,3,4],[0,1,2,2,3,2,3,4],[0,1,2,2,3,3,4,5],[0,1,2,2,3,4,3,5],
             [0,1,2,2,3,4,5,3],[0,1,2,2,3,4,5,4],[0,1,2,3,1,2,3,4],[0,1,2,3,2,2,3,4],[0,1,2,3,2,3,3,4],[0,1,2,3,2,3,4,5],
             [0,1,2,3,3,4,5,6],[0,2,1,2,3,3,4,5],[1,0,1,2,2,3,3,4],[1,0,1,2,2,3,4,3],[1,0,1,2,3,2,3,4],[1,0,1,2,3,3,4,5],
             [2,0,1,2,3,3,4,5]]
const A8 = [0,1,1,2,1,2,2,3]
const B8 = [0,1,1,2,2,3,3,4]

# chains_refined.out: n => (arrangements, both, one, none) under E2, E3*
const EXPECTED_REFINED = Dict(
    4 => (75, 0, 0, 75), 5 => (541, 0, 0, 541), 6 => (4683, 0, 4, 4679),
    7 => (47293, 0, 136, 47157), 8 => (545835, 18, 3068, 542749))
const BOTH18 = [
    [0, 0, 1, 2, 1, 2, 2, 3], [0, 0, 1, 2, 1, 2, 3, 3], [0, 1, 0, 1, 2, 3, 3, 4], [0, 1, 1, 2, 1, 2, 2, 3],
    [0, 1, 1, 2, 1, 2, 3, 3], [0, 1, 1, 2, 1, 2, 3, 4], [0, 1, 1, 2, 2, 3, 3, 4], [0, 1, 1, 2, 2, 3, 4, 3],
    [0, 1, 1, 2, 3, 2, 3, 4], [0, 1, 1, 2, 3, 4, 3, 4], [0, 1, 2, 1, 2, 3, 3, 4], [0, 1, 2, 1, 2, 3, 4, 3],
    [0, 1, 2, 2, 3, 3, 4, 5], [0, 1, 2, 3, 2, 3, 3, 4], [0, 1, 2, 3, 2, 3, 4, 5], [1, 0, 1, 2, 2, 3, 3, 4],
    [1, 0, 1, 2, 2, 3, 4, 3], [1, 0, 1, 2, 3, 2, 3, 4]]
# fine_model.out: (arrangement, abstract edges, cycles, states passing C1+C2, states passing C3 with one
# round of E3*, states passing C3 with E3* iterated)
const EXPECTED_FINE = [
    ([0, 0, 1, 2, 1, 2, 2, 3], 15, 14, 3000, 0, 0),
    ([0, 0, 1, 2, 1, 2, 3, 3], 16, 20, 10816, 0, 0),
    ([0, 1, 0, 1, 2, 3, 3, 4], 18, 22, 57344, 352, 0),
    ([0, 1, 1, 2, 1, 2, 2, 3], 16, 12, 5448, 165, 165),
    ([0, 1, 1, 2, 1, 2, 3, 3], 15, 14, 3000, 0, 0),
    ([0, 1, 1, 2, 1, 2, 3, 4], 17, 21, 17600, 176, 0),
    ([0, 1, 1, 2, 2, 3, 3, 4], 17, 32, 9905, 269, 269),
    ([0, 1, 1, 2, 2, 3, 4, 3], 17, 24, 12656, 0, 0),
    ([0, 1, 1, 2, 3, 2, 3, 4], 17, 28, 14016, 44, 0),
    ([0, 1, 1, 2, 3, 4, 3, 4], 18, 22, 57344, 352, 0),
    ([0, 1, 2, 1, 2, 2, 3, 4], 16, 21, 7152, 0, 0),
    ([0, 1, 2, 1, 2, 3, 3, 4], 17, 28, 14016, 44, 0),
    ([0, 1, 2, 1, 2, 3, 4, 3], 17, 22, 18432, 0, 0),
    ([0, 1, 2, 1, 3, 2, 3, 4], 17, 20, 19968, 0, 0),
    ([0, 1, 2, 2, 1, 2, 3, 4], 16, 18, 9344, 0, 0),
    ([0, 1, 2, 2, 3, 2, 3, 4], 16, 21, 7152, 0, 0),
    ([0, 1, 2, 2, 3, 3, 4, 5], 19, 32, 66304, 0, 0),
    ([0, 1, 2, 2, 3, 4, 3, 5], 19, 20, 104448, 0, 0),
    ([0, 1, 2, 2, 3, 4, 5, 3], 20, 22, 208896, 0, 0),
    ([0, 1, 2, 2, 3, 4, 5, 4], 19, 22, 98304, 0, 0),
    ([0, 1, 2, 3, 1, 2, 3, 4], 18, 23, 39936, 0, 0),
    ([0, 1, 2, 3, 2, 2, 3, 4], 16, 18, 9344, 0, 0),
    ([0, 1, 2, 3, 2, 3, 3, 4], 17, 21, 17600, 176, 0),
    ([0, 1, 2, 3, 2, 3, 4, 5], 19, 30, 79872, 0, 0),
    ([0, 1, 2, 3, 3, 4, 5, 6], 22, 26, 933888, 0, 0),
    ([0, 2, 1, 2, 3, 3, 4, 5], 19, 20, 104448, 0, 0),
    ([1, 0, 1, 2, 2, 3, 3, 4], 17, 24, 12656, 0, 0),
    ([1, 0, 1, 2, 2, 3, 4, 3], 17, 16, 15872, 0, 0),
    ([1, 0, 1, 2, 3, 2, 3, 4], 17, 22, 18432, 0, 0),
    ([1, 0, 1, 2, 3, 3, 4, 5], 19, 22, 98304, 0, 0),
    ([2, 0, 1, 2, 3, 3, 4, 5], 20, 22, 208896, 0, 0)]
# chains9.out and fine9.out
const EXPECTED_NINE = (7087261, 920, 60912, 7025429)
const NINE_BOTH_CHECKSUM = 65345741433      # sum over the 920 of the arrangement read as a decimal number
const NINE_REMAIN = (101, 5429609613, 2273, 44518, 2856998)   # number left, the same checksum, sums of abstract
                                                              # edges, coarse witnesses and admissible states

# ---------------------------------------------------------------- Section 2: the fine model
"abstract edges (a, b, kind, parities): kind 1 up, 2 run, 3 down; the up edges come first"
function abstract_graph(s)
    n = length(s)
    edges = Tuple{Int,Int,Int,Int}[]
    for a in 1:n, b in a+1:n
        s[b] == s[a] + 1 && push!(edges, (a, b, 1, 0))
    end
    for a in 1:n, b in 1:n
        a == b && continue
        beta = s[a] - s[b]
        if beta >= 1
            xs = get(L.RUNS, (beta, b < a), Int[])
            if !isempty(xs)
                par = 0
                for x in xs
                    par |= 1 << mod(s[a] - x, 2)
                end
                push!(edges, (a, b, 2, par))
            end
        end
        b < a && s[b] == s[a] - 5 && push!(edges, (a, b, 3, 0))
    end
    return edges
end

function adjacency(edges, n)
    adj = [Tuple{Int,Int}[] for _ in 1:n]
    for (i, e) in enumerate(edges)
        push!(adj[e[1]], (e[2], i - 1))
    end
    return adj
end

function simple_paths!(out, adj, v, c, vis::UInt64, mask::UInt64)
    for (w, i) in adj[v]
        (vis >> w) & 1 == 1 && continue
        if w == c
            push!(out, mask | (UInt64(1) << i))
        else
            simple_paths!(out, adj, w, c, vis | (UInt64(1) << w), mask | (UInt64(1) << i))
        end
    end
    return out
end

function simple_cycles!(out, adj, start, v, vis::UInt64, mask::UInt64)
    for (w, i) in adj[v]
        if w == start
            push!(out, mask | (UInt64(1) << i))
        elseif w > start && (vis >> w) & 1 == 0
            simple_cycles!(out, adj, start, w, vis | (UInt64(1) << w), mask | (UInt64(1) << i))
        end
    end
    return out
end

struct FineData
    m::Int
    nu::Int
    upmask::UInt64
    cycles::Vector{UInt64}
    runcycles::Vector{Tuple{UInt64,Int}}          # cycles through a run, with the parities they admit
    pairs::Vector{Tuple{Vector{UInt64},Vector{UInt64}}}
end

function fine_data(s)
    n = length(s)
    edges = abstract_graph(s)
    m = length(edges)
    upmask = UInt64(0)
    for (i, e) in enumerate(edges)
        e[3] == 1 && (upmask |= UInt64(1) << (i - 1))
    end
    adj = adjacency(edges, n)
    cyc = UInt64[]
    for start in 1:n
        simple_cycles!(cyc, adj, start, start, UInt64(1) << start, UInt64(0))
    end
    cyc = sort!(unique!(cyc))
    runcyc = Tuple{UInt64,Int}[]
    for cm in cyc
        par = 0
        for i in 0:m-1
            if (cm >> i) & 1 == 1 && edges[i+1][3] == 2
                par |= edges[i+1][4]
            end
        end
        par != 0 && push!(runcyc, (cm, par))
    end
    prs = Tuple{Vector{UInt64},Vector{UInt64}}[]
    for a in 1:n, c in a+1:n
        if s[c] == s[a] + 2
            ps = simple_paths!(UInt64[], adj, a, c, UInt64(1) << a, UInt64(0))
            two = [p for p in ps if p & ~upmask == 0 && count_ones(p) == 2]
            push!(prs, (ps, two))
        end
    end
    return FineData(m, count_ones(upmask), upmask, cyc, runcyc, prs)
end

"conditions C1, C2 on the state with dead set NG"
function pass_c12(d::FineData, NG::UInt64)
    for cm in d.cycles
        NG & cm == 0 && return false
    end
    for (ps, two) in d.pairs
        cnt = 0
        for p in ps
            NG & p == 0 && (cnt += 1)
        end
        if cnt == 1
            for t in two
                NG & t == 0 && return false
            end
        end
    end
    return true
end

"conditions C4 (rounds of E3*) and C3: does the state reach both parities?"
function pass_c34(d::FineData, NG::UInt64, rounds::Int)
    etadead = UInt64(0)
    for _ in 1:rounds
        new = etadead
        for (ps, two) in d.pairs
            live = false; cnt = 0
            for p in ps
                out = NG & p
                pc = count_ones(out)
                live |= pc == 0
                cnt += (pc == 1 && out & etadead == 0)
            end
            if !live && cnt == 1
                for t in two
                    out = NG & t
                    if count_ones(out) == 1 && out & etadead == 0
                        new |= out
                    end
                end
            end
        end
        new == etadead && break
        etadead = new
    end
    reach = 0
    for (cm, pm) in d.runcycles
        out = NG & cm
        if count_ones(out) == 1 && out & etadead == 0
            reach |= pm
        end
    end
    return reach == 3
end

"(abstract edges, cycles, states passing C1+C2, states passing C3 after one round of E3*, after E3* iterated);
up_parts: only the states whose set of live up edges is one of up_parts"
function analyse(s; up_parts=nothing)
    d = fine_data(s)
    full = (UInt64(1) << d.m) - 1
    a12 = 0; nb0 = 0; nb = 0
    function state(G::UInt64)
        NG = ~G & full
        if pass_c12(d, NG)
            a12 += 1
            pass_c34(d, NG, 1) && (nb0 += 1)
            pass_c34(d, NG, 8) && (nb += 1)
        end
    end
    if up_parts === nothing
        for g in UInt64(0):full
            state(g)
        end
    else
        @assert d.upmask == (UInt64(1) << d.nu) - 1
        for u in up_parts, rest in UInt64(0):(UInt64(1)<<(d.m-d.nu))-1
            state((rest << d.nu) | u)
        end
    end
    return d.m, length(d.cycles), a12, nb0, nb
end

# ---------------------------------------------------------------- Section 3: the second implementation
function edges_of(s)
    n = length(s)
    E = Tuple{Symbol,Int,Int,Vector{Int}}[]
    for a in 1:n, b in 1:n
        a == b && continue
        b > a && s[b] - s[a] == 1 && push!(E, (:up, a, b, Int[]))
        d = s[a] - s[b]
        if d >= 1 && !isempty(get(L.RUNS, (d, b < a), Int[]))
            push!(E, (:run, a, b, sort!(unique!([mod(s[a] - x, 2) for x in L.RUNS[(d, b < a)]]))))
        end
        d == 5 && b < a && push!(E, (:down, a, b, Int[]))
    end
    return E
end

function all_paths(E, a, c)
    res = Vector{Int}[]
    function rec(v, seen, path)
        for (i, e) in enumerate(E)
            (e[2] != v || e[3] in seen) && continue
            if e[3] == c
                push!(res, vcat(path, i))
            else
                rec(e[3], vcat(seen, e[3]), vcat(path, i))
            end
        end
    end
    rec(a, [a], Int[])
    return res
end

function all_cycles(E, n)
    res = Set{Vector{Int}}()
    for a in 1:n, (i, e) in enumerate(E)
        (e[2] != a || e[3] == a) && continue
        for q in all_paths(E, e[3], a)
            push!(res, sort!(vcat(i, q)))
        end
    end
    return collect(res)
end

"number of admissible states, state by state"
function count_states(s)
    n = length(s)
    E = edges_of(s)
    m = length(E)
    isup = [e[1] == :up for e in E]
    cyc = all_cycles(E, n)
    prs = [all_paths(E, a, c) for a in 1:n for c in 1:n if s[c] - s[a] == 2 && c > a]
    live = falses(m)
    zero = falses(m); new = falses(m)
    good = 0
    for bits in 0:(1<<m)-1
        for i in 1:m
            live[i] = (bits >> (i - 1)) & 1 == 1
        end
        any(c -> all(i -> live[i], c), cyc) && continue                                    # C1
        bad = false
        for ps in prs                                                                      # C2
            nl = 0; last = 0
            for (j, p) in enumerate(ps)
                if all(i -> live[i], p)
                    nl += 1; last = j
                end
            end
            if nl == 1 && length(ps[last]) == 2 && all(i -> isup[i], ps[last])
                bad = true; break
            end
        end
        bad && continue
        fill!(zero, false)                                                                 # C4, iterated
        while true
            copyto!(new, zero)
            for ps in prs
                any(p -> all(i -> live[i], p), ps) && continue
                nc = 0; cp = 0; ce = 0
                for (j, p) in enumerate(ps)
                    nout = 0; e = 0
                    for i in p
                        if !live[i]
                            nout += 1; e = i
                        end
                    end
                    if nout == 1 && !zero[e]
                        nc += 1; cp = j; ce = e
                    end
                end
                if nc == 1 && length(ps[cp]) == 2 && all(i -> isup[i], ps[cp])
                    new[ce] = true
                end
            end
            new == zero && break
            copyto!(zero, new)
        end
        par = 0                                                                            # C3
        for c in cyc
            nout = 0; e = 0
            for i in c
                if !live[i]
                    nout += 1; e = i
                end
            end
            if nout == 1 && !zero[e]
                for i in c
                    if E[i][1] == :run
                        for p in E[i][4]
                            par |= 1 << p
                        end
                    end
                end
            end
        end
        par == 3 && (good += 1)
    end
    return m, good
end

# ---------------------------------------------------------------- Section 4: the coarse witnesses
"dead sets of up edges passing E2 and reaching both parities after E3*, runs and down edges live"
function coarse_witnesses(s)
    up, adj, cyc, prs = L.coarse_data(s)
    out = UInt64[]
    for z in 0:(1<<length(up))-1
        z0 = UInt64(z)
        L.e2_bad(prs, z0) && continue
        dead = L.e3star_dead(prs, z0)
        L.reach_par(cyc, z0, dead) == 3 && push!(out, z0)
    end
    return length(up), out
end

"(abstract edges, coarse witnesses, admissible states among the states over the coarse witnesses)"
function work(s)
    nu, wit = coarse_witnesses(s)
    edges = abstract_graph(s)
    up = L.graph(s)[1]
    @assert [(e[1], e[2]) for e in edges[1:nu]] == up && all(e[3] != 1 for e in edges[nu+1:end])
    full = (UInt64(1) << nu) - 1
    parts = [full & ~z0 for z0 in wit]
    m, _, _, _, nb = analyse(s; up_parts=parts)
    return m, length(wit), nb
end

decimal(conf) = foldl((x, d) -> 10x + d, conf; init=0)
tup(conf) = "(" * join(conf, ", ") * ")"

"is the arrangement of nine one of the two open arrangements of eight with one line bundle added?"
function extends_open(conf)
    for i in eachindex(conf)
        rest = [conf[j] for j in eachindex(conf) if j != i]
        rest .-= minimum(rest)
        (rest == A8 || rest == B8) && return true
    end
    return false
end

function enumerate_refined(n; unrefined=false)
    total = 0; one = 0; none = 0
    both = Vector{Int}[]
    both_e3 = Vector{Int}[]
    L.contiguous_each(n) do conf
        total += 1
        c = L.classify(conf; refined=true)
        if c == 2
            push!(both, copy(conf))
        elseif c == 1
            one += 1
        else
            none += 1
        end
        if unrefined && L.classify(conf) == 2
            push!(both_e3, copy(conf))
        end
    end
    return (total, length(both), one, none), sort!(both), sort!(both_e3)
end

function main(args)
    nine = !("--no-nine" in args)
    npass = 0; nfail = 0
    function check(name, ok)
        println(ok ? "PASS " : "FAIL ", name)
        flush(stdout)
        ok ? (npass += 1) : (nfail += 1)
    end

    # Section 1
    both8 = Vector{Int}[]; both8_e3 = Vector{Int}[]
    for n in 4:8
        got, both, both_e3 = enumerate_refined(n; unrefined=(n == 8))
        check("E3* $n line bundles: $(got[1]) arrangements with interval shifts; both parities $(got[2]), one parity " *
              "$(got[3]), none $(got[4])" * (got == EXPECTED_REFINED[n] ? "" : "  (expected $(EXPECTED_REFINED[n]))"),
              got == EXPECTED_REFINED[n])
        n == 8 && ((both8, both8_e3) = (both, both_e3))
    end
    for conf in both8
        println("      both: ", tup(conf))
    end
    check("E3* eight line bundles: the 18 arrangements are those of chains_refined.out, all among the 31 of rule E3",
          both8 == BOTH18 && both8_e3 == sort(C31) && issubset(both8, C31))

    # Section 2
    rows = [(conf, analyse(conf)...) for conf in C31]
    for (conf, m, nc, a12, nb0, nb) in rows
        println("      ", tup(conf), ": $m abstract edges, $nc cycles, $a12 states pass C1+C2, $nb0 pass C3 with one round " *
                "of E3*, $nb with E3* iterated -> ", nb > 0 ? "OPEN" : "EXCLUDED")
    end
    check("fine model: edges, cycles, states passing C1+C2 and states passing C3 (one round, iterated) of the 31 " *
          "arrangements as in fine_model.out", rows == EXPECTED_FINE)
    surv = [r for r in rows if r[6] > 0]
    check("fine model: $(length(rows) - length(surv)) of $(length(rows)) arrangements have no admissible state, " *
          "$(length(surv)) remain", length(rows) == 31 && length(surv) == 2)
    check("fine model: (0, 1, 1, 2, 1, 2, 2, 3) has 165 admissible states", any(r -> r[1] == A8 && r[6] == 165, surv))
    check("fine model: (0, 1, 1, 2, 2, 3, 3, 4) has 269 admissible states", any(r -> r[1] == B8 && r[6] == 269, surv))

    # Section 3
    ok = true
    for r in rows
        m, good = count_states(r[1])
        ok &= (m == r[2] && good == r[6])
    end
    check("second implementation: the number of abstract edges and of admissible states agree on all 31 arrangements", ok)

    # Section 4
    ok = true; wA = 0; wB = 0
    for r in rows
        m, nw, nb = work(r[1])
        ok &= (m == r[2] && nb == r[6])
        r[1] == A8 && (wA = nw)
        r[1] == B8 && (wB = nw)
    end
    check("states over the coarse witnesses: the same admissible states on all 31 arrangements; $wA and $wB coarse " *
          "witnesses on the two that remain", ok && wA == 212 && wB == 76)

    # Section 5
    if nine
        got, both9, _ = enumerate_refined(9)
        check("E3* 9 line bundles: $(got[1]) arrangements with interval shifts; both parities $(got[2]), one parity " *
              "$(got[3]), none $(got[4])", got == EXPECTED_NINE)
        check("E3* nine line bundles: the 920 arrangements are those of chains9.out (checksum $(sum(decimal, both9; init=0)))",
              length(both9) == 920 && sum(decimal, both9; init=0) == NINE_BOTH_CHECKSUM)
        left = Tuple{Vector{Int},Int,Int,Int}[]
        for conf in both9
            m, nw, nb = work(conf)
            nb > 0 && push!(left, (conf, m, nw, nb))
        end
        for (conf, m, nw, nb) in left
            println("      remains: ", tup(conf), "  ($m abstract edges, $nw coarse witnesses, $nb admissible states)")
        end
        check("nine line bundles: $(length(both9) - length(left)) of $(length(both9)) excluded by C1-C4, $(length(left)) remain",
              length(both9) - length(left) == 819 && length(left) == 101)
        sums = (length(left), sum(r -> decimal(r[1]), left; init=0), sum(r -> r[2], left; init=0),
                sum(r -> r[3], left; init=0), sum(r -> r[4], left; init=0))
        check("nine line bundles: the 101 arrangements, their abstract edges, coarse witnesses and admissible states are " *
              "those of fine9.out (sums $(sums[3]), $(sums[4]), $(sums[5]))", sums == NINE_REMAIN)
        check("nine line bundles: each of the 101 is (0, 1, 1, 2, 1, 2, 2, 3) or (0, 1, 1, 2, 2, 3, 3, 4) with one line " *
              "bundle added", !isempty(left) && all(r -> extends_open(r[1]), left))
    else
        println("      nine line bundles: skipped (--no-nine)")
    end
    println("line_bundle_fine.jl: $npass checks passed, $nfail failed")
    return nfail
end

end # module

if abspath(PROGRAM_FILE) == @__FILE__
    exit(LineBundleFine.main(ARGS) > 0 ? 1 : 0)
end
