# Pieces outside every closed chain at the CM point A_0 = E_0^6 (Proposition VI.14 and Corollary VI.15).
# Julia port of code/cm_point_chains.py, on the Ext dimensions and Chern characters of cm_point_counts.jl.
#
# Gamma is the directed graph on the pieces with an edge u -> v (u != v) when
# Ext^{1 + s_u - s_v}(F_u, F_v) != 0.  A threefold piece on no cycle of Gamma is chain-free.
#   (A) the named configurations of Table III;
#   (B) family (a) over its window: 2401 polarised configurations, no closed chain;
#   (C) the sixteen pieces at the top shift are entered by no piece of positive twist at a shift at most
#       one above them (all zeta in mu_4^3, twists 1..4, shifts -3..2) and by no base piece; a piece at
#       shift 3 does enter them;
#   (D) family (c) over an enlarged window: 3024 polarised configurations, each with at least fifteen
#       chain-free threefold pieces; the polarised shape holds exactly when both pairs have shifts of
#       opposite parity;
#   (E) four or five line bundles (twists 1..5, shifts -3..3) with the thirty-two at shifts 0, 1: one of
#       the two classes of sixteen pieces is chain-free; with L^1[-2], ..., L^6[3] every piece lies on a cycle.
#
#   julia --startup-file=no cm_point_chains.jl
#
# Exact arithmetic only; no packages.

include(joinpath(@__DIR__, "cm_point_counts.jl"))

module CMPointChains

using ..CMPointCounts
const K = CMPointCounts

"is ch(E) of the polarised shape with N != 0 ?"
function polarised_config(pieces)
    ch = Form()
    for p in pieces
        ch = fadd(ch, piece_ch(p))
    end
    ok, N, _ = polarised(ch)
    return ok && !iszero(N)
end

const EXTDEG = Dict{Tuple{Symbol,NTuple{3,Int},Int,Symbol,NTuple{3,Int},Int},Int}()
"bit mask of the degrees k with Ext^k(p, q) != 0"
function ext_nonzero_degrees(p::Piece, q::Piece)
    get!(EXTDEG, (p.kind, p.zeta, p.twist, q.kind, q.zeta, q.twist)) do
        dims, _ = ext_dims(p, q)
        m = 0
        for (k, v) in dims
            v > 0 && (m |= 1 << k)
        end
        m
    end
end

function edge(p::Piece, q::Piece)
    k = 1 + p.shift - q.shift
    return 0 <= k <= 6 && (ext_nonzero_degrees(p, q) >> k) & 1 == 1
end

edges(pieces) = [[b for b in eachindex(pieces) if b != a && edge(pieces[a], pieces[b])] for a in eachindex(pieces)]

"The pieces lying on a cycle of Gamma: the vertices of the strongly connected components of size at
least two (Tarjan)."
function on_cycle(pieces)
    E = edges(pieces)
    n = length(pieces)
    index = fill(-1, n); low = fill(-1, n); onstack = falses(n)
    stack = Int[]; out = Set{Int}()
    counter = 0
    function strong(v)
        index[v] = low[v] = counter
        counter += 1
        push!(stack, v); onstack[v] = true
        for w in E[v]
            if index[w] < 0
                strong(w)
                low[v] = min(low[v], low[w])
            elseif onstack[w]
                low[v] = min(low[v], index[w])
            end
        end
        if low[v] == index[v]
            comp = Int[]
            while true
                w = pop!(stack)
                onstack[w] = false
                push!(comp, w)
                w == v && break
            end
            length(comp) >= 2 && union!(out, comp)
        end
    end
    for v in 1:n
        index[v] < 0 && strong(v)
    end
    return out
end

function chain_free_threefolds(pieces)
    oc = on_cycle(pieces)
    return [a for (a, p) in enumerate(pieces) if p.kind == :Z && !(a in oc)], oc
end

Ls(spec) = [Lpiece(l, t) for (l, t) in spec]

function main()
    npass = 0; nfail = 0
    function check(name, ok)
        println(ok ? "PASS " : "FAIL ", name)
        flush(stdout)
        ok ? (npass += 1) : (nfail += 1)
    end
    z111 = ZETAS[1]
    @assert z111 == (0, 0, 0)
    B = base()
    top = [a for (a, p) in enumerate(B) if p.shift == 1]
    bottom = [a for (a, p) in enumerate(B) if p.shift == 0]
    check("thirty-two base pieces, sixteen at each shift", length(B) == 32 && length(top) == 16 && length(bottom) == 16)

    # (A) the named configurations
    base35 = vcat(B, Ls([(1, 0), (2, 0), (3, 0)]))
    free, oc = chain_free_threefolds(base35)
    check("(A) thirty-five pieces: no closed chain", isempty(oc) && length(free) == 32)
    famA = vcat(B, Ls([(1, -2), (2, -1), (3, 0), (4, 1)]))
    free, oc = chain_free_threefolds(famA)
    check("(A) family (a) at L^1[-2], L^2[-1], L^3[0], L^4[1]: no closed chain", polarised_config(famA) && isempty(oc))
    famC = vcat(B, [Zpiece(z111, 1, -1), Zpiece(z111, 1, 0), Zpiece(z111, 2, 1), Zpiece(z111, 2, 2)], Ls([(1, 0), (2, 0), (3, 0)]))
    free, oc = chain_free_threefolds(famC)
    expected_on = union(Set(a for (a, p) in enumerate(famC) if p.kind == :Z && p.twist > 0),
                        Set(a for a in bottom if zmeet(B[a].zeta, z111)[1] >= 1),
                        Set(a for (a, p) in enumerate(famC) if p.kind == :L && p.twist == 2))
    check("(A) family (c): $(length(free)) chain-free threefold pieces (expected twenty-two), the sixteen at shift 1 and " *
          "the six at shift 0 disjoint from Z_(1,1,1); on cycles: the four extra copies, the ten pieces at shift 0 " *
          "meeting Z_(1,1,1) and L^2[0]",
          polarised_config(famC) && length(free) == 22 && issubset(top, free) && oc == expected_on)
    partner = [z for z in ZETAS if zmeet(z111, z)[1] == 2][1]
    famD = vcat(B, [Zpiece(partner, 0, 0), Zpiece(partner, 0, 1)], Ls([(1, 0), (2, 0), (3, 0)]))
    free, oc = chain_free_threefolds(famD)
    check("(A) family (d): $(length(free)) chain-free threefold pieces (expected twenty-eight)",
          polarised_config(famD) && length(free) == 28)

    # (B) family (a) over the window of Table III
    count = 0; ncyc = 0
    K.product_each(collect(-3:3), 4) do ts
        pcs = vcat(B, Ls(zip((1, 2, 3, 4), ts)))
        polarised_config(pcs) || return
        count += 1
        isempty(on_cycle(pcs)) || (ncyc += 1)
    end
    check("(B) family (a), four line bundles L^1..L^4 at shifts -3..3: $count polarised configurations, " *
          "$ncyc with a closed chain", count == 2401 && ncyc == 0)

    # (C) nothing of positive twist at a shift at most one above the top enters a top piece
    entrants = copy(B)
    for a in 0:3, b in 0:3, c in 0:3, k in 1:4, s in -3:2
        push!(entrants, Zpiece((a, b, c), k, s))
    end
    for l in 1:4, t in -3:2
        push!(entrants, Lpiece(l, t))
    end
    bad = [(i, v) for (i, u) in enumerate(entrants) for v in top if i != v && edge(u, B[v])]
    check("(C) no edge into a top piece from the base or from $(length(entrants) - 32) pieces of positive twist at " *
          "shifts -3..2", isempty(bad) && length(entrants) - 32 == 1560)
    sharp = all(edge(Lpiece(l, 3), B[v]) for l in 1:4 for v in top) && all(edge(Zpiece(z111, 1, 3), B[v]) for v in top)
    check("(C) pieces at shift 3 do enter the top pieces: L^l[3] and Z_(1,1,1) L^1[3]", sharp)

    # (D) family (c) over the enlarged window
    tot = 0; bad_c = 0; least = 99; parity_ok = true
    for (k1, k2) in K.combinations(collect(1:3), 2), s1 in -3:3, s1b in s1:3, s2 in -3:3, s2b in s2:3
        extra = [Zpiece(z111, k1, s1), Zpiece(z111, k1, s1b), Zpiece(z111, k2, s2), Zpiece(z111, k2, s2b)]
        for t in -3:3
            pcs = vcat(B, extra, Ls([(1, t), (2, t), (3, t)]))
            pol = polarised_config(pcs)
            parity_ok &= (pol == (isodd(s1 - s1b) && isodd(s2 - s2b)))
            pol || continue
            tot += 1
            free, _ = chain_free_threefolds(pcs)
            least = min(least, length(free))
            isempty(free) && (bad_c += 1)
        end
    end
    check("(D) family (c), two further twists 1 <= k < k' <= 3, pairs at shifts -3..3, L^1, L^2, L^3 at a common " *
          "shift -3..3: $tot polarised configurations, least number of chain-free threefold pieces $least, " *
          "$bad_c without one", tot == 3024 && least == 15 && bad_c == 0)
    check("(D) the polarised shape holds exactly when both pairs have shifts of opposite parity", parity_ok)

    # (E) four or five line bundles of positive twist with the thirty-two at shifts 0, 1
    tot = 0; bad_e = 0
    topset = Set(top); bottomset = Set(bottom)
    for nL in (4, 5), ls in K.combinations(collect(1:5), nL)
        K.product_each(collect(-3:3), nL) do ts
            pcs = vcat(B, Ls(zip(ls, ts)))
            tot += 1
            _, oc = chain_free_threefolds(pcs)
            top_free = isempty(intersect(oc, topset))
            bottom_free = isempty(intersect(oc, bottomset))
            (top_free || bottom_free) || (bad_e += 1)
            shifts = Set(ts)
            !top_free && !issubset((-1, 0, 1, 2, 3), shifts) && (bad_e += 1)
            !bottom_free && !issubset((-2, -1, 0, 1, 2), shifts) && (bad_e += 1)
        end
    end
    check("(E) four or five line bundles, twists in 1..5, shifts in -3..3: $tot configurations; in each one class " *
          "of sixteen pieces is chain-free, and a class on cycles has line bundles at its five shifts ($bad_e " *
          "exceptions)", bad_e == 0 && tot == 28812)
    six = vcat(B, Ls([(1, -2), (2, -1), (3, 0), (4, 1), (5, 2), (6, 3)]))
    free, oc = chain_free_threefolds(six)
    check("(E) six line bundles L^1[-2], ..., L^6[3]: every piece lies on a cycle",
          polarised_config(six) && isempty(free) && length(oc) == 38)

    println("cm_point_chains.jl: $npass checks passed, $nfail failed")
    return nfail
end

end # module

if abspath(PROGRAM_FILE) == @__FILE__
    exit(CMPointChains.main() > 0 ? 1 : 0)
end
