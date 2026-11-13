# Lemma w:lem-invariant: on A = E_0^{2n}, n = 3, 4, the joint kernel of the tangent space T D of the polarised Weil
# family and of its complex conjugate, acting on H^*(A,C) = wedge^*(H^1) by derivations, is spanned by theta^k
# (k = 0..2n) and alpha, alpha-bar (degree 2n); the kernel of T D alone is much larger (dimension 344, 1696), so the
# reality of the class is used.  Generators dz_1..dz_N (0..N-1), dzbar_1..dzbar_N (N..2N-1), N = 2n; T D is spanned by
# v_ab = [dz_a -> dzbar_{n+b}] + [dz_{n+b} -> dzbar_a], a, b < n.  The operators preserve the torus weight, so the
# kernel splits by weight and degree; ranks are computed in exact Rational{BigInt} arithmetic.
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms
const QQ = Rational{BigInt}

function apply_D(g, h, mono::Vector{Int})
    (g in mono && !(h in mono)) || return nothing
    pos = findfirst(==(g), mono) - 1
    rest = [x for x in mono if x != g]
    k = count(<(h), rest)
    (iseven(pos + k) ? 1 : -1), sort(vcat(rest, [h]))
end
function rank_rows(rows)
    piv = Dict{Int,Dict{Int,QQ}}(); rk = 0
    for r0 in rows
        r = Dict{Int,QQ}(k => QQ(v) for (k, v) in r0 if v != 0)
        while !isempty(r)
            c = minimum(keys(r))
            if haskey(piv, c)
                f = r[c]
                for (k, v) in piv[c]
                    x = get(r, k, zero(QQ)) - f * v
                    iszero(x) ? delete!(r, k) : (r[k] = x)
                end
            else
                f = r[c]; piv[c] = Dict(k => v / f for (k, v) in r); rk += 1; break
            end
        end
    end
    rk
end
combs(N, k) = k == 0 ? [Int[]] : [vcat(s, [x]) for s in combs(N, k - 1) for x in (isempty(s) ? 0 : s[end] + 1):N-1]

function run(n)
    N = 2n
    wt(g) = g < N ? (g, g < n ? 1 : -1) : (g - N, g - N < n ? -1 : 1)
    ops = Vector{Vector{Tuple{Int,Int}}}()
    for a in 0:n-1, b in 0:n-1
        push!(ops, [(a, N + n + b), (n + b, N + a)])
        push!(ops, [(N + a, n + b), (N + n + b, a)])
    end
    tdonly = ops[1:2:end]
    spaces = Dict{Tuple{Vector{Int},Int},Vector{Vector{Int}}}()
    for k in 0:2N, mono in combs(2N, k)
        w = zeros(Int, N)
        for g in mono; j, s = wt(g); w[j+1] += s end
        push!(get!(spaces, (w, k), Vector{Int}[]), mono)
    end
    total = Dict{Tuple{String,Int},Int}(); total_td = 0
    for ((w, d), ms) in spaces
        idx = Dict(m => i for (i, m) in enumerate(ms))
        for (opset, joint) in ((ops, true), (tdonly, false))
            rows = Dict{Tuple{Int,Vector{Int}},Dict{Int,Int}}()
            for (oi, op) in enumerate(opset), m in ms, (g, h) in op
                r = apply_D(g, h, m); r === nothing && continue
                s, t = r; row = get!(rows, (oi, t), Dict{Int,Int}())
                row[idx[m]] = get(row, idx[m], 0) + s
            end
            kd = length(ms) - rank_rows(collect(values(rows)))
            kd == 0 && continue
            if joint
                cls = all(==(0), w) ? "zero" : all(==(1), w) ? "plus" : all(==(-1), w) ? "minus" : string(w)
                total[(cls, d)] = get(total, (cls, d), 0) + kd
            else
                total_td += kd
            end
        end
    end
    expected = Dict{Tuple{String,Int},Int}(("zero", 2k) => 1 for k in 0:N)
    expected[("plus", N)] = 1; expected[("minus", N)] = 1
    total == expected, total_td
end

C = Checks("inv_check.jl")
for (n, tdk) in ((3, 344), (4, 1696))
    ok, ntd = run(n)
    check(C, "n=$n: joint kernel of T D and its conjugate = span(theta^k) + span(alpha, alpha-bar)", ok)
    check(C, "n=$n: kernel of T D alone has dimension $ntd", ntd == tdk)
end
finish(C)
