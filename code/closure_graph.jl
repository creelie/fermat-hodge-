# closure_graph.jl -- the closure graph of Sect. III of the paper, in Julia.
# Run: julia closure_graph.jl
const STMTS = ["HC", "F3", "F2", "F3p", "L", "M", "V", "AB"]
const RULES = [(["HC"], "F3"), (["F3"], "HC"), (["HC"], "F2"), (["HC"], "F3p"),
               (["HC"], "AB"), (["F2"], "AB"), (["AB"], "F2"), (["AB", "F3p"], "HC"),
               (["L", "M"], "HC"), (["L"], "AB"), (["V"], "AB"), (["HC"], "M")]
idx(x) = findfirst(==(x), STMTS)
function closure(mask::Int)
    while true
        new = mask
        for (prem, c) in RULES
            pm = sum(1 << (idx(p) - 1) for p in prem)
            if pm & mask == pm
                new |= 1 << (idx(c) - 1)
            end
        end
        new == mask && return mask
        mask = new
    end
end
hc = 1 << (idx("HC") - 1)
derive = Set(m for m in 0:255 if closure(m) & hc != 0)
cand = [m for m in 0:255 if m & hc == 0]
minimal = [m for m in cand if m in derive &&
           !any(t in derive for t in cand if t != m && t & m == t)]
names(m) = "{" * join([STMTS[i] for i in 1:8 if m & (1 << (i - 1)) != 0], ",") * "}"
println("subsets: 256  deriving HC: ", length(derive))
println("minimal sufficient sets: ", length(minimal))
for m in sort(minimal, by = m -> (count_ones(m), m))
    println("  ", names(m))
end
expected = Set(sum(1 << (idx(x) - 1) for x in s) for s in
               [["F3"], ["L", "M"], ["L", "F3p"], ["V", "F3p"], ["F2", "F3p"], ["AB", "F3p"]])
ok = Set(minimal) == expected
for s in [["F2"], ["F3p"], ["L"], ["M"], ["V"], ["AB"], ["L", "V"], ["M", "F3p"]]
    global ok &= !(sum(1 << (idx(x) - 1) for x in s) in derive)
end
println("closure_graph.jl: ", ok ? "PASS" : "FAIL")
exit(ok ? 0 : 1)
