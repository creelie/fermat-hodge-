# Proposition w:prop-cubesets: the unions of whole cubes whose Chern character lies in Q[theta] + W.
# A cube Q(zeta) of Proposition w:prop-cubes has ch E_Q = -(-1)^{c(zeta)} [Z_zeta], [Z_zeta] = m_1 m_2 m_3, for every
# twisting cochain.  In exact arithmetic over Q(i) (exterior algebra on 12 generators, Complex{Rational{BigInt}}):
# (1) sum_zeta -(-1)^c [Z_zeta] = -32(alpha + alpha-bar);
# (2) rank [theta^3, alpha, alpha-bar, 32 classes [Z_zeta]] = 25, so the signed combinations in Q theta^3 + W form a
#     space K of dimension 10;
# (3) exactly 44 sets U of cubes have signed sum in Q theta^3 + W: the empty set, all 32, and 42 sets of 16 cubes,
#     each with eight cubes of c = 0 and eight of c = 1 (so neither parity class alone is one of them).
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms
const QQ = Rational{BigInt}
const CQ = Complex{QQ}
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
const MU4 = (CQ(1), CQ(0, 1), CQ(-1), CQ(0, -1))
hi = CQ(0, QQ(1, 2))
bit(j) = UInt32(1) << (j - 1)                    # dz_j -> bit j-1, dzbar_k -> bit 6+k-1
function mform(j, a)                              # (i/2)(dz_j dzbar_j + dz_{3+j} dzbar_{3+j} + conj(a) dz_j dzbar_{3+j} + a dz_{3+j} dzbar_j)
    prune(Form(bit(j) | bit(6 + j) => hi, bit(3 + j) | bit(9 + j) => hi, bit(j) | bit(9 + j) => hi * conj(a), bit(3 + j) | bit(6 + j) => hi * a))
end
theta = Form(bit(j) | bit(6 + j) => hi for j in 1:6)
th3 = wedge(wedge(theta, theta), theta)
alpha = Form(UInt32(0) => one(CQ)); alphab = Form(UInt32(0) => one(CQ))
for j in 1:3
    global alpha = wedge(alpha, Form(bit(j) | bit(9 + j) => hi))
    global alphab = wedge(alphab, Form(bit(3 + j) | bit(6 + j) => hi))
end
cubes = Tuple{NTuple{3,Int},Int,Form}[]
for k1 in 0:3, k2 in 0:3, k3 in 0:3
    s = k1 + k2 + k3; isodd(s) && continue
    Zc = wedge(wedge(mform(1, MU4[k1+1]), mform(2, MU4[k2+1])), mform(3, MU4[k3+1]))
    push!(cubes, ((k1, k2, k3), mod(s, 4) == 0 ? 0 : 1, Zc))
end
eps = [c == 0 ? -1 : 1 for (_, c, _) in cubes]

C = Checks("subsets.jl")
tot = Form()
for (k, (_, _, Zc)) in enumerate(cubes), (m, v) in Zc; tot[m] = get(tot, m, zero(CQ)) + eps[k] * v end
target = Form(); for D in (alpha, alphab), (m, v) in D; target[m] = get(target, m, zero(CQ)) - 32v end
check(C, "sum_zeta -(-1)^c [Z_zeta] = -32(alpha + alpha-bar)", prune(tot) == prune(target))
mons = sort(collect(union(keys(th3), keys(alpha), keys(alphab), (keys(Zc) for (_, _, Zc) in cubes)...)))
cols = vcat([th3, alpha, alphab], [Zc for (_, _, Zc) in cubes])
M = [get(cols[j], mons[i], zero(CQ)) for i in 1:length(mons), j in 1:length(cols)]
piv = Int[]; r = 0
for c in 1:size(M, 2)
    p = findfirst(i -> !iszero(M[i, c]), r+1:size(M, 1)); p === nothing && continue
    p += r; global r += 1; M[[r, p], :] = M[[p, r], :]; M[r, :] = M[r, :] / M[r, c]
    for i in 1:size(M, 1); i != r && !iszero(M[i, c]) && (M[i, :] -= M[i, c] * M[r, :]) end
    push!(piv, c)
end
free = [c for c in 1:size(M, 2) if !(c in piv)]
check(C, "rank of [theta^3, alpha, alpha-bar, 32 cube classes] = $r; dim K = $(length(free))", r == 25 && length(free) == 10 && all(>(3), free))
kern = map(free) do f
    v = zeros(CQ, size(M, 2)); v[f] = 1
    for (row, pc) in enumerate(piv); v[pc] = -M[row, f] end
    v[4:end]
end
fc = free .- 3
sols = Vector{Int}[]
for bits in 0:(2^length(free) - 1)
    nu = zeros(CQ, 32)
    for t in 1:length(free); (bits >> (t - 1)) & 1 == 1 && (nu .+= eps[fc[t]] .* kern[t]) end
    x = Int[]
    for i in 1:32
        v = nu[i] * eps[i]
        v == 0 ? push!(x, 0) : v == 1 ? push!(x, 1) : break
    end
    length(x) == 32 && push!(sols, x)
end
sizes = sort([sum(x) for x in sols])
c0 = [c == 0 ? 1 : 0 for (_, c, _) in cubes]; c1 = 1 .- c0
check(C, "$(length(sols)) cube sets: sizes 0 (1), 16 ($(count(==(16), sizes))), 32 ($(count(==(32), sizes)))",
      length(sols) == 44 && sizes == vcat([0], fill(16, 42), [32]))
check(C, "each set of 16 has eight cubes with c = 0 and eight with c = 1; neither parity class is a solution",
      all(sum(x .* c0) == 8 for x in sols if sum(x) == 16) && !(c0 in sols) && !(c1 in sols))
finish(C)
