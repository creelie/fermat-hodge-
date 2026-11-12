# mumford_disc.jl -- port of rounds/r1-MUM/mum_disc.py: the discriminant of
# the Weil fourfold (A x E, k).
#
# H_1(A,Q) = K = F (x) k, F a totally real cubic field, with the k-hermitian
# form H_a(x,y) = Tr_{K/k}(a x ybar), a in F; on the k-basis 1, th, th^2 its
# matrix is Tr_{F/Q}(a th^(i+j)).  H_1(E,Q) = k with the form b x ybar, so
# det H = b det(Tr(a th^(i+j))).  Checked exactly, for the 342 nonzero
# a = a0 + a1 th + a2 th^2 with |a_i| <= 3 and four cubic fields:
#   det(Tr_{F/Q}(a th^(i+j))) = N_{F/Q}(a) disc(1, th, th^2);
#   if a has signs (-,-,+) in some order then N(a) > 0 and, with
#   b := N(a) disc, det H is the square of N(a) disc (discriminant 1).
# The signs of the conjugates are decided exactly, from the characteristic
# polynomial of a and a rational isolation of the roots of the cubic (the
# Python evaluates at floating-point roots).
# Run: julia --startup-file=no mumford_disc.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms: Checks, check, finish

const Q = Rational{BigInt}
det3(M) = M[1, 1] * (M[2, 2] * M[3, 3] - M[2, 3] * M[3, 2]) - M[1, 2] * (M[2, 1] * M[3, 3] - M[2, 3] * M[3, 1]) +
          M[1, 3] * (M[2, 1] * M[3, 2] - M[2, 2] * M[3, 1])
tr3(M) = M[1, 1] + M[2, 2] + M[3, 3]

"isolating rational intervals (lo, hi), of width < 2^-60, of the three real roots of x^3 + c2 x^2 + c1 x + c0, in increasing order"
function root_intervals(c2, c1, c0)
    f(x) = x^3 + c2 * x^2 + c1 * x + c0
    out = Tuple{Q,Q}[]
    for i in -40:39                                  # grid of step 1/4 on [-10, 10]
        lo, hi = Q(i // 4), Q((i + 1) // 4)
        f(lo) == 0 && error("rational root")
        sign(f(lo)) * sign(f(hi)) < 0 || continue
        for _ in 1:64
            mid = (lo + hi) / 2
            sign(f(lo)) * sign(f(mid)) <= 0 ? (hi = mid) : (lo = mid)
        end
        push!(out, (lo, hi))
    end
    return out
end
"exact sign of a0 + a1 r + a2 r^2 at the root r in (lo, hi) of the irreducible cubic f (so the value is nonzero)"
function sign_at(co, iv, c2, c1, c0)
    f(x) = x^3 + c2 * x^2 + c1 * x + c0
    g(x) = co[1] + co[2] * x + co[3] * x^2
    lo, hi = iv
    while true
        # g is monotone on [lo, hi] if its derivative keeps its sign there; otherwise shrink
        dlo, dhi = co[2] + 2 * co[3] * lo, co[2] + 2 * co[3] * hi
        if sign(dlo) * sign(dhi) >= 0 && sign(g(lo)) * sign(g(hi)) > 0
            return Int(sign(g(lo)))
        end
        mid = (lo + hi) / 2
        sign(f(lo)) * sign(f(mid)) <= 0 ? (hi = mid) : (lo = mid)
    end
end

function main()
    C = Checks("mumford_disc.jl")
    fields = ["Q(zeta7)^+ : x^3+x^2-2x-1" => (1, -2, -1, 49, 91, [(27, 1323), (43, 2107)]),
              "Q(zeta9)^+ : x^3-3x+1" => (0, -3, 1, 81, 91, [(81, 6561), (127, 10287)]),
              "disc 148 (S3): x^3-x^2-3x+1" => (-1, -3, 1, 148, 94, [(54, 7992), (67, 9916)]),
              "disc 229 (S3): x^3-4x-1" => (0, -4, -1, 229, 94, [(54, 12366), (64, 14656)])]
    for (name, (c2, c1, c0, disc_want, count_want, first_want)) in fields
        Cm = Q[0 0 -c0; 1 0 -c1; 0 1 -c2]            # multiplication by th
        P = [Cm^k for k in 0:4]
        disc = det3([tr3(P[i+j+1]) for i in 0:2, j in 0:2])
        ivs = root_intervals(c2, c1, c0)
        println(name, "  disc(1,th,th^2) = ", numerator(disc), "  roots ", [round(Float64(lo), digits = 4) for (lo, hi) in ivs])
        check(C, "$name: three real roots, disc(1, th, th^2) = $disc_want", length(ivs) == 3 && disc == disc_want)
        found = 0; nall = 0; okdet = true; oknorm = true; oksq = true; okdesc = true; firsts = Tuple{Int,Int}[]
        for a0 in -3:3, a1 in -3:3, a2 in -3:3
            co = (a0, a1, a2)
            co == (0, 0, 0) && continue
            nall += 1
            A = a0 * P[1] + a1 * P[2] + a2 * P[3]    # multiplication by a
            Na = det3(A)
            G = [tr3(A * P[i+j+1]) for i in 0:2, j in 0:2]
            okdet &= det3(G) == Na * disc
            signs = Tuple(sign_at(co, iv, c2, c1, c0) for iv in ivs)
            # cross-check with the characteristic polynomial x^3 - t x^2 + s x - n of a (Descartes; all roots real)
            t = tr3(A); s = (t^2 - tr3(A * A)) / 2
            cf = [v for v in (1, -t, s, -Na) if v != 0]
            okdesc &= count(i -> sign(cf[i]) != sign(cf[i+1]), 1:length(cf)-1) == count(==(1), signs)
            if sort(collect(signs)) == [-1, -1, 1]
                oknorm &= Na > 0
                b = Na * disc; detH = b * det3(G)
                r = isqrt(numerator(detH))
                oksq &= denominator(detH) == 1 && r * r == detH && r == Na * disc
                if found < 2
                    println("   a = $a0 + $a1 th + $a2 th^2, signs $signs, N(a) = $(numerator(Na)), det H_a = $(numerator(det3(G))), b = $(numerator(b)), det H = $(numerator(detH)) = $(r)^2")
                    push!(firsts, (Int(numerator(Na)), Int(numerator(b))))
                end
                found += 1
            end
        end
        check(C, "$name: det Tr(a th^(i+j)) = N(a) disc for all $nall a (expected 342)", okdet && nall == 342)
        check(C, "$name: the signs at the three roots agree with the count of positive roots of the characteristic polynomial of a", okdesc)
        check(C, "$name: $found a with signs (-,-,+) (expected $count_want), all with N(a) > 0", oknorm && found == count_want)
        check(C, "$name: for these, b = N(a) disc makes det H = (N(a) disc)^2, a rational square", oksq)
        check(C, "$name: the first two, (N(a), b) = $(first_want[1]) and $(first_want[2])", firsts == first_want)
    end
    finish(C)
end
main()
