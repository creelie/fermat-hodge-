# Theorem w:thm-nothingentersall without the hypothesis |t_i - p| >= 2, n = 3, 4.
# On each surface B_j a line bundle whose hermitian form has eigenvalues (l1, l2) has cohomology only in degrees
# [#neg, 2 - #pos] (Lemma w:lem-hqn). Pieces L_zeta (form [[p,z],[zbar,p]]) and M_i (form t_i Id); steps of degree one
# between distinct pieces have Ext degree q >= the lower end; L-L steps have excess >= 1 (excess_check.jl).
# Lower bound for the excess of every closed path of distinct pieces (four abstract L's, M_1..M_3),
# all placements t_i - p in {-5..5} distinct.
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms

function cycles(f::Function, N::Int)
    path = Int[]; used = falses(N)
    function rec()
        length(path) >= 2 && f(path)
        for x in 1:N
            (used[x] || x < path[1]) && continue
            push!(path, x); used[x] = true; rec(); pop!(path); used[x] = false
        end
    end
    for s in 1:N
        push!(path, s); used[s] = true; rec(); pop!(path); used[s] = false
    end
end
lowdeg(eigs) = sum((l1 < 0) + (l2 < 0) for (l1, l2) in eigs)

function run(n)
    minLL = 1
    worst_all = typemax(Int); worst_cfg = (); bad = 0
    nodes = ["L1", "L2", "L3", "L4", "M1", "M2", "M3"]
    for t1 in -5:5, t2 in -5:5, t3 in -5:5
        length(Set((t1, t2, t3))) == 3 || continue
        t = Dict("M1" => t1, "M2" => t2, "M3" => t3)
        function q(a, b)
            if startswith(a, "L")
                d = t[b]; return lowdeg(fill((d + 1, d - 1), n))
            elseif startswith(b, "L")
                d = -t[a]; return lowdeg(fill((d + 1, d - 1), n))
            else
                d = t[b] - t[a]; return lowdeg(fill((d, d), n))
            end
        end
        worst = typemax(Int)
        cycles(length(nodes)) do cyc
            k = length(cyc); e = 0
            for i in 1:k
                a, b = nodes[cyc[i]], nodes[cyc[mod1(i + 1, k)]]
                e += (startswith(a, "L") && startswith(b, "L")) ? minLL : q(a, b) - 1
            end
            worst = min(worst, e)
        end
        if worst < worst_all; worst_all = worst; worst_cfg = (t1, t2, t3) end
        worst < 1 && (bad += 1)
    end
    println("n=$n: min closed-path excess over all placements t-p in [-5,5]: $worst_all (at $worst_cfg); placements with excess <= 0: $bad")
    worst_all, bad
end

C = Checks("excess_general.jl")
w3, b3 = run(3); w4, b4 = run(4)
check(C, "n=3: min excess 1, no placement with excess <= 0", w3 == 1 && b3 == 0)
check(C, "n=4: min excess 2, no placement with excess <= 0", w4 == 2 && b4 == 0)
finish(C)
