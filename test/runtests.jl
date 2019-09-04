using JuliaVariables
using Test
using NameResolution

@testset "JuliaVariables.jl" begin
    ana, ex = solve(:(function f(x)
        let y = x + 1
            y
        end
    end))
    run_analyzer(ana)
    println(ana.children[1])
    println(ex)
    # Write your own tests here.
end
