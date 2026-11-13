# Combinatorial core of Theorem w:thm-nothingentersall for n = 3, 4 and |t_i - p| >= 2.
# A term of d_E landing in a diagonal block runs along a closed path of k >= 2 distinct pieces whose steps are
# morphisms of degree one (Ext degree q) with nonzero harmonic group; it needs total excess sum(q-1) = 0.
# (i) L_zeta -> L_zeta': the group sits in Ext degrees [m, 2n-m], m = number of differing coordinates, and q has the
#     parity of 1 + [prod zeta != prod zeta']; minimum excess over all ordered pairs.
# (ii) steps touching a multiple: q = 0 (excess -1, up the value) or q = 2n (excess 2n-1, down).
# (iii) every closed path of distinct nodes among four abstract L's and M_1, M_2, M_3, every rank of p among the t_i.
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms

# all closed paths (cycles with a distinguished minimal start) of k >= 2 distinct nodes from 1:N
function cycles(f::Function, N::Int)
    path = Int[]; used = falses(N)
    function rec()
        k = length(path)
        k >= 2 && f(path)
        for x in 1:N
            (used[x] || x < path[1]) && continue
            push!(path, x); used[x] = true; rec(); pop!(path); used[x] = false
        end
    end
    for s in 1:N
        push!(path, s); used[s] = true; rec(); pop!(path); used[s] = false
    end
end

function minLL(n)
    mu4 = [1, im, -1, -im]
    Z = [collect(z) for z in Iterators.product(ntuple(_ -> mu4, n)...) if prod(z) in (1, -1)]
    best = typemax(Int)
    for z in Z, w in Z
        z == w && continue
        m = count(i -> z[i] != w[i], 1:n)
        par = prod(z) == prod(w) ? 0 : 1
        qs = [q for q in m:2n-m if mod(q, 2) == mod(1 + par, 2)]
        isempty(qs) && continue
        best = min(best, minimum(qs) - 1)
    end
    length(Z), best
end

function worstpath(n, mLL)
    worst = typemax(Int)
    for prank in 0:3
        order = ["M1", "M2", "M3"]; insert!(order, prank + 1, "P")
        vals = Dict(name => r for (r, name) in enumerate(order))
        nodes = ["L1", "L2", "L3", "L4", "M1", "M2", "M3"]
        val(x) = startswith(x, "L") ? vals["P"] : vals[x]
        exc(a, b) = (startswith(a, "L") && startswith(b, "L")) ? mLL : (val(b) > val(a) ? -1 : 2n - 1)
        cycles(length(nodes)) do cyc
            k = length(cyc)
            e = sum(exc(nodes[cyc[i]], nodes[cyc[mod1(i + 1, k)]]) for i in 1:k)
            worst = min(worst, e)
        end
    end
    worst
end

C = Checks("excess_check.jl")
for n in (3, 4)
    nz, mLL = minLL(n)
    w = worstpath(n, mLL)
    println("n=$n: min L-L excess over $(nz)^2 ordered pairs = $mLL; min closed-path excess = $w")
    check(C, "n=$n: min L-L excess = 1", mLL == 1)
    check(C, "n=$n: min closed-path excess = 2 (nothing enters the diagonal)", w == 2)
end
finish(C)
