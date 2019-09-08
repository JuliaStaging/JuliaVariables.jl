using JuliaVariables
using Test
using NameResolution

rmlines = JuliaVariables.rmlines
JuliaVariables.@quick_lambda begin
@testset "JuliaVariables.jl" begin
    func = solve(:(function f(x)
        let y = x + 1
            y
        end
    end))
    println(func |> rmlines)

    func = solve(:(function f(x)
        y = x + 1
        z -> z + y
    end))

    println(func |> rmlines)

    func = solve(:(function f(x)
        y = x + 1
        let y = y + 1
            (x + y  + z for z in 1:10)
        end
    end))
    println(func |> rmlines)

    func = solve(
        macroexpand(@__MODULE__,:(
        @inline function f(x)
            y = x + 1
            let y = y + 1
                (x + y  + z for z in 1:10)
            end
        end
    )))
    println(func |> rmlines)
    # @test map(haskey(func.scope.freevars, _), [])

    func = solve_from_local(quote
        a -> a + z
    end)
    println(func |> rmlines)

    func = solve_from_local(quote
    q = a
    function z(x, k=1)
        (x=x, k=k, q=q)
    end
    end)
    println(func |> rmlines)
    # Write your own tests here.

    a = solve(:(function k(x::T) where T
                  :(1, T)
              end
    ))
    @test haskey(a.scope.bounds, :T)
end
end
