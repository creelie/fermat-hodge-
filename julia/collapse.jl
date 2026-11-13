# Theorem w:thm-koszulcubes, Lemma w:lem-cubewindows and the strong connectivity of the window graph of the
# configuration of Proposition w:prop-cubes on A = E_0^6.  Two models of the degree-zero twists:
#   maximal: every Ext group allowed by its window is nonzero (an upper bound for all twists);
#   generic: product twists inside each cube, the 32 twists P_0(zeta) independent and generic, so that the groups
#            between pieces of different cubes with degenerate difference vanish (Lemma w:lem-cubewindows(d)).
# (A) the 260-piece window graph is strongly connected in both models (37252 and 1668 edges);
# (B) with every cube replaced by its Koszul object O_{Z'} (x) N [-(3+c)] the 36-piece graph is acyclic in both models,
#     with the edge types C->A, C->D, A->B, D->B, D->Z@3, Z@4->A and (maximal model only) Z@4->Z@3;
# (C) generic model: in every cube every entry piece is contained in every exit piece;
# (D) one cube collapsed, the other 252 pieces kept: the collapsed piece is chain-free for 32 of 32 cubes in the
#     generic model and for 4 of 32 in the maximal model.
# Inertia is computed exactly from the 2x2 blocks of the forms (all forms are block diagonal for B_j = (z_j, z_{3+j})).
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms

# ---- hermitian forms as three 2x2 blocks (a_j, d_j, b_j): H[j,j] = a, H[3+j,3+j] = d, H[3+j,j] = b
struct Herm; a::NTuple{3,Int}; d::NTuple{3,Int}; b::NTuple{3,Complex{Int}}; end
Base.:-(x::Herm, y::Herm) = Herm(x.a .- y.a, x.d .- y.d, x.b .- y.b)
Base.:+(x::Herm, y::Herm) = Herm(x.a .+ y.a, x.d .+ y.d, x.b .+ y.b)
const MU4 = (1 + 0im, 0 + 1im, -1 + 0im, 0 - 1im)
zeroH() = Herm((0, 0, 0), (0, 0, 0), (0im, 0im, 0im))
mform(j, a) = Herm(ntuple(k -> k == j ? 1 : 0, 3), ntuple(k -> k == j ? 1 : 0, 3), ntuple(k -> k == j ? a : 0im, 3))
tI(t) = Herm((t, t, t), (t, t, t), (0im, 0im, 0im))
function inertia(H::Herm)            # (n_-, n_+), complex counts
    neg = 0; pos = 0
    for j in 1:3
        a, d, b = H.a[j], H.d[j], H.b[j]; det = a * d - abs2(b); tr = a + d
        if det > 0; tr > 0 ? (pos += 2) : (neg += 2)
        elseif det < 0; neg += 1; pos += 1
        elseif tr > 0; pos += 1
        elseif tr < 0; neg += 1
        end
    end
    neg, pos
end

struct Pc; H::Herm; d::Int; cube::Int; S::Vector{Int}; t::Int; end
cubes = Tuple{NTuple{3,Int},Int}[]
for k1 in 0:3, k2 in 0:3, k3 in 0:3
    s = k1 + k2 + k3; isodd(s) && continue
    push!(cubes, ((k1, k2, k3), mod(s, 4) == 0 ? 0 : 1))
end
pieces = Pc[]
for (ci, (z, c)) in enumerate(cubes), S in ([Int[]], [[1], [2], [3]], [[1, 2], [1, 3], [2, 3]], [[1, 2, 3]])
    for s in S
        H = zeroH(); for j in s; H += mform(j, MU4[z[j] + 1]) end
        push!(pieces, Pc(H, length(s) + c, ci, s, 0))
    end
end
const TS = [(-2, -1), (-1, 0), (3, 4), (4, 5)]
for (t, d) in TS; push!(pieces, Pc(tI(t), d, 0, Int[], t)) end
V = length(pieces)
cubeof(P) = P.cube
qdeg(x::Pc, y::Pc) = 1 + x.d - y.d
function gamma(model)
    E = Dict{Tuple{Int,Int},Int}()
    for a in 1:V, b in 1:V
        a == b && continue
        neg, pos = inertia(pieces[b].H - pieces[a].H); q = qdeg(pieces[a], pieces[b])
        if neg + pos == 6
            q == neg && (E[(a, b)] = q)
        elseif neg <= q <= 6 - pos
            cross = pieces[a].cube > 0 && pieces[b].cube > 0 && pieces[a].cube != pieces[b].cube
            (model == :maximal || !cross) && (E[(a, b)] = q)
        end
    end
    E
end
function strongly_connected(n, E)
    adj = [Int[] for _ in 1:n]; radj = [Int[] for _ in 1:n]
    for (a, b) in E; push!(adj[a], b); push!(radj[b], a) end
    function reach(adj)
        seen = falses(n); seen[1] = true; st = [1]
        while !isempty(st); v = pop!(st); for w in adj[v]; seen[w] || (seen[w] = true; push!(st, w)) end end
        all(seen)
    end
    reach(adj) && reach(radj)
end
function acyclic(n, E)
    indeg = zeros(Int, n); adj = [Int[] for _ in 1:n]
    for (a, b) in E; push!(adj[a], b); indeg[b] += 1 end
    st = [v for v in 1:n if indeg[v] == 0]; seen = 0
    while !isempty(st); v = pop!(st); seen += 1; for w in adj[v]; indeg[w] -= 1; indeg[w] == 0 && push!(st, w) end end
    seen == n
end
# the restriction of a block-diagonal form to T Z_zeta, basis w_j = zeta_j e_j - e_{3+j}: diagonal entries
restr(H::Herm, z) = [H.a[j] + H.d[j] - 2 * real(H.b[j] * MU4[z[j] + 1]) for j in 1:3]
inert3(v) = (count(<(0), v), count(>(0), v))
ext_ZM(z, H) = (n = inert3(restr(H, z)); (3 + n[1], 6 - n[2], n[1] + n[2] == 3))   # Ext^k(O_Z (x) N, M)
ext_MZ(z, H) = (n = inert3(restr(H, z)); (n[2], 3 - n[1], n[1] + n[2] == 3))       # Ext^k(M, O_Z (x) N)

C = Checks("collapse.jl")
GA = Dict(m => gamma(m) for m in (:maximal, :generic))
for (m, ne) in ((:maximal, 37252), (:generic, 1668))
    check(C, "(A) $m model: $(length(GA[m])) edges, strongly connected", length(GA[m]) == ne && strongly_connected(V, keys(GA[m])))
end
# (B) the collapsed configuration: 32 objects Z (shift 3 + c) and the four theta-bundles
struct Cp; isZ::Bool; z::NTuple{3,Int}; d::Int; H::Herm; name::String; end
col = vcat([Cp(true, z, 3 + c, zeroH(), "Z") for (z, c) in cubes],
           [Cp(false, (0, 0, 0), d, tI(t), string("ABCD"[k])) for (k, (t, d)) in enumerate(TS)])
function col_edges(model)
    E = Dict{Tuple{Int,Int},Int}(); n = length(col)
    for a in 1:n, b in 1:n
        a == b && continue
        x, y = col[a], col[b]; q = 1 + x.d - y.d
        if x.isZ && y.isZ
            dd = count(j -> x.z[j] == y.z[j], 1:3)
            model == :generic && dd > 0 && continue
            lo, hi = dd == 0 ? (3, 3) : (3 - dd, 3 + dd)
            lo <= q <= hi && (E[(a, b)] = q)
        elseif x.isZ || y.isZ
            lo, hi, nd = x.isZ ? ext_ZM(x.z, y.H) : ext_MZ(y.z, x.H)
            (nd ? q == lo : lo <= q <= hi) && (E[(a, b)] = q)
        else
            neg, pos = inertia(y.H - x.H)
            (neg + pos == 6 ? q == neg : neg <= q <= 6 - pos) && (E[(a, b)] = q)
        end
    end
    E
end
for m in (:maximal, :generic)
    E = col_edges(m); types = Dict{String,Int}()
    for ((a, b), q) in E
        k = string(col[a].name, col[a].isZ ? "@$(col[a].d)" : "", "->", col[b].name, col[b].isZ ? "@$(col[b].d)" : "", " q=$q")
        types[k] = get(types, k, 0) + 1
    end
    want = Dict("C->A q=6" => 1, "C->D q=0" => 1, "A->B q=0" => 1, "D->B q=6" => 1, "D->Z@3 q=3" => 16, "Z@4->A q=6" => 16)
    m == :maximal && (want["Z@4->Z@3 q=2"] = 144)
    check(C, "(B) $m model: collapsed 36-piece graph acyclic, edge types $(join(sort(["$k:$v" for (k, v) in types]), ", "))",
          acyclic(length(col), keys(E)) && types == want)
end
# (C)
let E = GA[:generic], good = true
    for ci in 1:length(cubes)
        Q = Set(i for i in 1:V if pieces[i].cube == ci)
        exits = Set(pieces[a].S for (a, b) in keys(E) if a in Q && !(b in Q))
        entries = Set(pieces[b].S for (a, b) in keys(E) if b in Q && !(a in Q))
        good &= all(issubset(n, e) for n in entries for e in exits)
    end
    check(C, "(C) generic model: in all 32 cubes every entry piece is contained in every exit piece", good)
end
# (D)
for (m, want) in ((:maximal, 4), (:generic, 32))
    free = 0
    for (ci, (z, c)) in enumerate(cubes)
        keep = [i for i in 1:V if pieces[i].cube != ci]; ren = Dict(i => k + 1 for (k, i) in enumerate(keep))
        ed = [(ren[a], ren[b]) for (a, b) in keys(GA[m]) if haskey(ren, a) && haskey(ren, b)]
        for i in keep
            M = pieces[i]; cross = M.cube > 0
            for dir in (0, 1)
                q = dir == 0 ? 1 + (3 + c) - M.d : 1 + M.d - (3 + c)
                lo, hi, nd = dir == 0 ? ext_ZM(z, M.H) : ext_MZ(z, M.H)
                if nd ? q == lo : (lo <= q <= hi && (m == :maximal || !cross))
                    push!(ed, dir == 0 ? (1, ren[i]) : (ren[i], 1))
                end
            end
        end
        n = length(keep) + 1; adj = [Int[] for _ in 1:n]
        for (a, b) in ed; push!(adj[a], b) end
        seen = falses(n); st = copy(adj[1]); for w in st; seen[w] = true end
        while !isempty(st); v = pop!(st); for w in adj[v]; seen[w] || (seen[w] = true; push!(st, w)) end end
        seen[1] || (free += 1)
    end
    check(C, "(D) $m model: a single collapsed cube is chain-free for $free of 32 cubes", free == want)
end
finish(C)
