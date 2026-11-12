# closure_graph.jl -- the closure graph of Sect. III of the paper and the
# finite checks of Sect. VIII.  Port of code/closure_graph.py (and of the
# earlier code/closure_graph.jl) and of code/bypass_checks.py.
#
# (1) Eight statements HC, F3, F2, F3p, L, M, V, AB and twelve rules (Table I).
#     The closure of all 256 subsets; 230 derive HC; the minimal subsets of
#     the seven hypotheses deriving HC are exactly {F3}, {L,M}, {L,F3p},
#     {V,F3p}, {F2,F3p}, {AB,F3p}.
# (2) The extended rule table of Sect. VIII: HC_ab is not derived from the
#     proved or quoted base, the minimal sufficient sets, two equivalences.
# (3) Blow-up bookkeeping (Manin's formula): the defect never decreases.
# Run: julia --startup-file=no closure_graph.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms: Checks, check, finish

function closure(seed, rules)
    s = Set(seed)
    while true
        new = setdiff(Set(c for (prem, c) in rules if all(in(s), prem)), s)
        isempty(new) && return s
        union!(s, new)
    end
end

subsets(v) = [[v[i] for i in 1:length(v) if (m >> (i - 1)) & 1 == 1] for m in 0:(1 << length(v))-1]

function combinations(v, k)
    out = Vector{Vector{eltype(v)}}()
    function rec(start, cur)
        if length(cur) == k
            push!(out, copy(cur)); return
        end
        for i in start:length(v)
            push!(cur, v[i]); rec(i + 1, cur); pop!(cur)
        end
    end
    rec(1, eltype(v)[])
    return out
end

function main()
    C = Checks("closure_graph.jl")

    # ---- (1) the closure graph of Sect. III ----------------------------------
    STMTS = ["HC", "F3", "F2", "F3p", "L", "M", "V", "AB"]
    RULES = [(["HC"], "F3"), (["F3"], "HC"), (["HC"], "F2"), (["HC"], "F3p"),
             (["HC"], "AB"), (["F2"], "AB"), (["AB"], "F2"), (["AB", "F3p"], "HC"),
             (["L", "M"], "HC"), (["L"], "AB"), (["V"], "AB"), (["HC"], "M")]
    allsets = [Set(s) for s in subsets(STMTS)]
    derive = Set(s for s in allsets if "HC" in closure(s, RULES))
    hyps = filter(!=("HC"), STMTS)
    cand = [Set(s) for s in subsets(hyps)]
    minimal = [s for s in cand if s in derive && !any(t in derive for t in cand if t != s && issubset(t, s))]
    sort!(minimal, by = s -> (length(s), sort(collect(s))))
    println("subsets: ", length(allsets), "  deriving HC: ", length(derive))
    println("minimal sufficient sets: ", length(minimal))
    for s in minimal
        println("  {", join(sort(collect(s), by = x -> findfirst(==(x), STMTS)), ","), "}")
    end
    expected = Set(Set(x) for x in [["F3"], ["L", "M"], ["L", "F3p"], ["V", "F3p"], ["F2", "F3p"], ["AB", "F3p"]])
    check(C, "256 subsets of the eight statements", length(allsets) == 256 && length(Set(allsets)) == 256)
    check(C, "230 subsets derive HC", length(derive) == 230)
    check(C, "6 minimal sufficient sets: {F3}, {L,M}, {L,F3p}, {V,F3p}, {F2,F3p}, {AB,F3p}",
          length(minimal) == 6 && Set(minimal) == expected)
    check(C, "a subset derives HC iff it contains HC or one of the six minimal sets",
          all((s in derive) == ("HC" in s || any(issubset(e, s) for e in expected)) for s in allsets))
    check(C, "{F2}, {F3p}, {L}, {M}, {V}, {AB}, {L,V}, {M,F3p} do not derive HC",
          all(!(Set(s) in derive) for s in [["F2"], ["F3p"], ["L"], ["M"], ["V"], ["AB"], ["L", "V"], ["M", "F3p"]]))
    # the same counts with bit masks (the implementation of the earlier closure_graph.jl)
    idx(x) = findfirst(==(x), STMTS)
    mask(s) = sum((1 << (idx(x) - 1) for x in s); init = 0)
    function closure_mask(m)
        while true
            new = m
            for (prem, c) in RULES
                pm = mask(prem)
                pm & m == pm && (new |= 1 << (idx(c) - 1))
            end
            new == m && return m
            m = new
        end
    end
    hc = mask(["HC"])
    derive_m = Set(m for m in 0:255 if closure_mask(m) & hc != 0)
    cand_m = [m for m in 0:255 if m & hc == 0]
    minimal_m = [m for m in cand_m if m in derive_m && !any(t in derive_m for t in cand_m if t != m && t & m == t)]
    check(C, "bit-mask implementation: 230 deriving HC and the same six minimal sets",
          length(derive_m) == 230 && Set(minimal_m) == Set(mask(collect(e)) for e in expected) &&
          derive_m == Set(mask(collect(s)) for s in derive))

    # ---- (2) the rules of Sect. VIII (bypass_checks.py) ----------------------
    R8 = [(["HC_ab", "red_ab"], "HC"), (["red_ab"], "HC_ab"), (["HC_ab", "red_ab_mod"], "HC"),
          (["weil_all", "red_weil"], "HC_ab"), (["weil_iq", "weil_cm"], "weil_all"),
          (["weil_triv", "weil_nontriv"], "weil_iq"),
          (["base_point", "reduction", "orbit_dense", "P2_iq_s"], "weil_triv"),
          (["base_point", "reduction", "orbit_dense", "P2_iq_ns"], "weil_nontriv"),
          (["base_point_cm", "reduction_cm", "orbit_dense_cm", "P2_cm_s"], "weil_cm_triv"),
          (["base_point_cm", "reduction_cm", "orbit_dense_cm", "P2_cm_ns"], "weil_cm_nontriv"),
          (["weil_cm_triv", "weil_cm_nontriv"], "weil_cm"), (["weil_triv"], "weil_nontriv"),
          (["weil_cm_triv"], "weil_cm_nontriv"), (["weil_cm_triv"], "weil_triv"),
          (["lef_B", "mot"], "HC"), (["lef_B", "mot_def"], "vhc"), (["vhc", "acc_ab"], "HC_ab"),
          (["red_weil"], "HC_ab"),
          (["lef_B_absch"], "vhc_absch"), (["vhc_absch", "acc_ab"], "HC_ab"), (["HC_ab"], "vhc_absch"),
          (["lef_B"], "lef_B_absch"), (["lef_B"], "lef_B_ab"), (["vhc"], "vhc_absch"), (["mot"], "mot_ab"),
          (["HC"], "red_ab"), (["HC"], "HC_ab"), (["HC"], "red_weil"), (["HC"], "red_ab_mod")]
    BASE = ["base_point", "reduction", "orbit_dense", "base_point_cm", "reduction_cm",
            "orbit_dense_cm", "mot_def", "acc_ab", "lef_B_ab", "mot_ab"]
    OPEN = ["red_ab", "red_ab_mod", "red_weil", "P2_iq_s", "P2_iq_ns", "P2_cm_s",
            "P2_cm_ns", "lef_B", "mot", "vhc", "lef_B_absch", "vhc_absch"]
    function minimal_sets(goal; maxsize = 3)
        found = Vector{Vector{String}}()
        for k in 1:maxsize, S in combinations(OPEN, k)
            any(issubset(T, S) for T in found) && continue
            goal in closure(vcat(BASE, S), R8) && push!(found, S)
        end
        return found
    end
    cl = closure(BASE, R8)
    println("closure of proved/quoted + {lef_B_ab, mot_ab}: ", sort(collect(cl)))
    check(C, "the closure of the proved or quoted base is the base itself (29 rules, 10 facts)",
          length(R8) == 29 && cl == Set(BASE))
    for g in ("HC_ab", "HC", "vhc_absch", "lef_B_absch")
        check(C, "$g is not derived from the base", !(g in cl))
    end
    mab = minimal_sets("HC_ab"); mhc = minimal_sets("HC")
    println("minimal sufficient sets for HC_ab: ", mab)
    println("minimal sufficient sets for HC: ", mhc)
    check(C, "minimal sufficient sets for HC_ab: red_ab, red_weil, lef_B, vhc, lef_B_absch, vhc_absch",
          mab == [["red_ab"], ["red_weil"], ["lef_B"], ["vhc"], ["lef_B_absch"], ["vhc_absch"]])
    check(C, "minimal sufficient sets for HC: {red_ab}, {red_ab_mod, x} for x = red_weil, lef_B, vhc, lef_B_absch, vhc_absch, and {lef_B, mot}",
          mhc == [["red_ab"], ["red_ab_mod", "red_weil"], ["red_ab_mod", "lef_B"], ["red_ab_mod", "vhc"],
                  ["red_ab_mod", "lef_B_absch"], ["red_ab_mod", "vhc_absch"], ["lef_B", "mot"]])
    check(C, "HC_ab <=> vhc_absch (given acc_ab)",
          "HC_ab" in closure(vcat(BASE, "vhc_absch"), R8) && "vhc_absch" in closure(vcat(BASE, "HC_ab"), R8))
    check(C, "lef_B_absch => HC_ab", "HC_ab" in closure(vcat(BASE, "lef_B_absch"), R8))
    check(C, "HC_ab does not give lef_B_absch", !("lef_B_absch" in closure(vcat(BASE, "HC_ab"), R8)))

    # ---- (3) blow-up bookkeeping ----------------------------------------------
    # defX[d], defZ[d]: dim Hdg^d - dim Alg^d for X and Z; centre of codimension c
    defect_blowup(defX, defZ, c, p) = get(defX, p, 0) + sum(get(defZ, p - k, 0) for k in 1:c-1)
    defX = Dict(2 => 2)
    check(C, "blow-up: the defect of Bl_Z(X x X) in degree 4 is never smaller than that of X x X",
          all(defect_blowup(defX, defZ, c, 2) >= defX[2] for c in (2, 3, 4)
              for defZ in (Dict{Int,Int}(), Dict(1 => 1), Dict(0 => 0, 1 => 2))))
    check(C, "blow-up: the Weil defect is preserved for n = 2..5",
          all(defect_blowup(Dict(n => 2), Dict(n - 1 => 1), c, n) >= 2 for n in 2:5 for c in (2, 3)))
    finish(C)
end
main()
