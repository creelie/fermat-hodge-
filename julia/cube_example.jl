# Proposition w:prop-cubes: the configuration of 260 line bundles on A = E_0^6 that passes every graph test.
# Coordinates z_1..z_6, blocks B_j = (z_j, z_{3+j}); f_{j,a} = z_j + a z_{3+j}, a in mu_4, m_{j,a} = c_1(f_{j,a}^* O(0)),
# whose hermitian form is [[1, conj a], [a, 1]] on B_j.  32 cubes zeta in mu_4^3 with prod zeta = +-1 (c = 0 resp. 1),
# pieces M_S(zeta) at shift |S| + c, and four multiples (t, shift) = (-2,-1), (-1,0), (3,4), (4,5) of theta.
# All forms are block diagonal for the B_j, so inertia is computed exactly from the 2x2 blocks (determinant, trace).
# (1) sum_pieces (-1)^shift e^{c_1} = -32(alpha + alpha-bar) + p(theta) exactly (exterior algebra on 12 generators
#     over Q(i), Complex{Rational{BigInt}}), and the Hankel rank of p is 3, so r = 57;
# (2) the windows of the Koszul edges contain q = 0 (up) and q = 2 (down), and the cross link has q = 1 both ways;
# (3) the graph Gamma_0 of 196 edges with nondegenerate difference, 384 + 384 Koszul edges and the 2 link edges is
#     strongly connected, with 385 two-cycles.
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms
const QQ = Rational{BigInt}
const CQ = Complex{QQ}

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

# ---- exterior algebra over Q(i): dz_j bit j-1, dzbar_k bit 6+k-1
const Form = Dict{UInt32,CQ}
prune(f::Form) = filter(p -> !iszero(p.second), f)
function wedge(A::Form, B::Form)
    out = Form()
    for (ma, ca) in A, (mb, cb) in B
        ma & mb != 0 && continue
        s = 0; x = mb
        while x != 0; y = trailing_zeros(x); x &= x - one(UInt32); s += count_ones(ma >> (y + 1)) end
        out[ma | mb] = get(out, ma | mb, zero(CQ)) + (isodd(s) ? -1 : 1) * ca * cb
    end
    prune(out)
end
function addf!(A::Form, B::Form, c)
    for (m, v) in B; A[m] = get(A, m, zero(CQ)) + c * v end
    A
end
function form_of(H::Herm)            # (i/2) sum H_jk dz_j ^ dzbar_k
    f = Form(); hi = CQ(0, QQ(1, 2))
    put(j, k, v) = iszero(v) || (f[(UInt32(1) << (j - 1)) | (UInt32(1) << (6 + k - 1))] = get(f, (UInt32(1) << (j - 1)) | (UInt32(1) << (6 + k - 1)), zero(CQ)) + hi * v)
    for j in 1:3
        put(j, j, H.a[j]); put(3 + j, 3 + j, H.d[j]); put(3 + j, j, H.b[j]); put(j, 3 + j, conj(H.b[j]))
    end
    prune(f)
end
function expo(c::Form)
    res = Form(UInt32(0) => one(CQ)); term = Form(UInt32(0) => one(CQ))
    for k in 1:6
        term = Form(m => v / k for (m, v) in wedge(term, c)); isempty(term) && break
        addf!(res, term, 1)
    end
    prune(res)
end
function weilpair()
    al = Form(UInt32(0) => one(CQ)); ab = Form(UInt32(0) => one(CQ))
    for j in 0:2
        al = wedge(al, Form((UInt32(1) << j) | (UInt32(1) << (9 + j)) => CQ(0, QQ(1, 2))))
        ab = wedge(ab, Form((UInt32(1) << (3 + j)) | (UInt32(1) << (6 + j)) => CQ(0, QQ(1, 2))))
    end
    al, ab
end
function qrank(M::Matrix{QQ})
    M = copy(M); r = 0
    for c in 1:size(M, 2)
        p = findfirst(i -> !iszero(M[i, c]), r+1:size(M, 1)); p === nothing && continue
        p += r; r += 1; M[[r, p], :] = M[[p, r], :]
        for i in 1:size(M, 1); i != r && (M[i, :] -= M[i, c] / M[r, c] * M[r, :]) end
    end
    r
end

C = Checks("cube_example.jl")
let total = Form()
    for P in pieces; addf!(total, expo(form_of(P.H)), iseven(P.d) ? 1 : -1) end
    al, ab = weilpair(); target = Form()
    addf!(target, al, -32); addf!(target, ab, -32)
    th = form_of(tI(1))
    for (t, d) in TS; addf!(target, expo(Form(m => t * v for (m, v) in th)), iseven(d) ? 1 : -1) end
    check(C, "$V pieces, $(length(cubes)) cubes: ch(E) = -32(alpha + alpha-bar) + p(theta)", prune(addf!(total, target, -1)) == Form())
    Hk = [sum(QQ((iseven(d) ? 1 : -1) * big(t)^(i + j)) for (t, d) in TS) for i in 0:4, j in 0:2]
    rk = qrank(Hk)
    check(C, "Hankel rank of p is $rk, r(gamma) = $((4 + rk) * 9 - 6)", rk == 3 && (4 + rk) * 9 - 6 == 57)
end
qdeg(a, b) = 1 + pieces[a].d - pieces[b].d
function window(a, b)
    neg, pos = inertia(pieces[b].H - pieces[a].H); neg, 6 - pos, neg + pos == 6
end
edges = Set{Tuple{Int,Int}}(); kinds = Dict{String,Int}()
function try_edge(a, b, why)
    lo, hi, nd = window(a, b); q = qdeg(a, b)
    ok = nd ? q == lo : lo <= q <= hi
    ok && (push!(edges, (a, b)); kinds[why] = get(kinds, why, 0) + 1)
    ok
end
for a in 1:V, b in 1:V
    a == b && continue
    lo, hi, nd = window(a, b)
    nd && qdeg(a, b) == lo && (push!(edges, (a, b)); kinds["nondegenerate"] = get(kinds, "nondegenerate", 0) + 1)
end
idx = Dict((P.cube, P.S) => i for (i, P) in enumerate(pieces) if P.cube > 0)
bad = 0
for ci in 1:length(cubes), S in ([Int[]], [[1], [2], [3]], [[1, 2], [1, 3], [2, 3]]), s in S, j in setdiff(1:3, s)
    a = idx[(ci, s)]; b = idx[(ci, sort(vcat(s, [j])))]
    try_edge(a, b, "up") || (global bad += 1)
    try_edge(b, a, "down") || (global bad += 1)
end
zp = findfirst(x -> x[2] == 0, cubes); zm = findfirst(x -> x[2] == 1 && x[1][1] == cubes[zp][1][1], cubes)
X = idx[(zp, [1, 2])]; Y = idx[(zm, [1])]
l1 = try_edge(X, Y, "link"); l2 = try_edge(Y, X, "link")
check(C, "every Koszul window contains its degree (up q = 0, down q = 2): $(kinds["up"]) + $(kinds["down"]) edges", bad == 0 && kinds["up"] == 384 && kinds["down"] == 384)
check(C, "cross link M_12(zeta+) <-> M_1(zeta-) at shift 2: q = 1 both ways, difference of inertia $(inertia(pieces[Y].H - pieces[X].H))",
      l1 && l2 && inertia(pieces[Y].H - pieces[X].H) == (1, 0))
check(C, "$(kinds["nondegenerate"]) edges with nondegenerate difference", kinds["nondegenerate"] == 196)
function reach(src, adj)
    seen = falses(V); seen[src] = true; st = [src]
    while !isempty(st); v = pop!(st); for w in adj[v]; seen[w] || (seen[w] = true; push!(st, w)) end end
    count(seen)
end
adj = [Int[] for _ in 1:V]; radj = [Int[] for _ in 1:V]
for (a, b) in edges; push!(adj[a], b); push!(radj[b], a) end
two = count(e -> (e[2], e[1]) in edges, edges) ÷ 2
check(C, "Gamma_0 ($(length(edges)) edges) is strongly connected, with $two two-cycles",
      reach(1, adj) == V && reach(1, radj) == V && two == 385)
finish(C)
