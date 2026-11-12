# run_all.jl -- runs every check program of this directory in a fresh Julia
# process and prints its final line; exits with code 1 if any program fails.
# Run: julia --startup-file=no run_all.jl
const here = @__DIR__
const progs = sort(filter(f -> endswith(f, ".jl") && f != "run_all.jl", readdir(here)))
let failed = 0, total = 0
    for f in progs
        out = IOBuffer()
        ok = success(pipeline(`$(Base.julia_cmd()) --startup-file=no $(joinpath(here, f))`; stdout=out, stderr=out))
        lines = split(strip(String(take!(out))), '\n')
        last = isempty(lines) ? "" : lines[end]
        m = match(r"(\d+) checks passed, (\d+) failed", last)
        m === nothing || (total += parse(Int, m[1]))
        ok || (failed += 1)
        println(ok ? "ok    " : "FAIL  ", last)
    end
    println("run_all.jl: ", length(progs), " programs, ", total, " checks passed, ", failed, " programs failed")
    exit(failed == 0 ? 0 : 1)
end
