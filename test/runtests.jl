using JuliaVariables
using Test
using NameResolution
using MLStyle

rmlines(ex::Expr) = begin
    hd = ex.head
    tl = map(rmlines, filter(!islinenumbernode, ex.args))
    Expr(hd, tl...)
end
rmlines(@nospecialize(a)) = a
islinenumbernode(@nospecialize(x)) = x isa LineNumberNode


get_fn_scope(ex) =
    @match ex begin
        Expr(
            :scoped,
            _,
            Expr(:function, _,
                Expr(:scoped, scope, _)
            )
        ) => scope
        _ => error("malformed $ex")
    end

get_fn_body(ex) =
    @match ex begin
        Expr(
            :scoped,
            _,
            Expr(:function, _,
                Expr(:scoped, _, body)
            )
        ) => body
        _ => error("malformed $ex")
    end

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
            for z in 1:10
                x + y + z
            end
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
                (1, T)
              end
    ))

    @test any(x -> x.name == :T, get_fn_scope(a).bounds)

    # a = solve(:(2 .^ [2, 3]))
    # @test eval(a) == [4, 8]

    a = solve(:(function z(x, k=1)
                   x + 20 + a + k
               end
    ))

    @test any(x -> x.name == :k, get_fn_scope(a).bounds)


    a = solve(:(function z(x, k=1)
                   (k=k, )
               end
    ))

    @test any(x -> x.name == :k, get_fn_scope(a).bounds)

    @test @when :(k=$_, ) = get_fn_body(a).args[2] begin
        true
    @otherwise
        false
    end

    func = solve(:(function (x)
              z = x + 1
              y -> begin
                  z += 1
                  z
              end
          end))

    println(func |> rmlines)
    @test any(x -> x.name == :z && x.is_mutable, get_fn_scope(func).bounds)

    func = solve(macroexpand(@__MODULE__, :(@inline function (x)
              z = x + 1
              @inline function (y)
                  z += 1
                  z
              end
          end)))
    println(func |> rmlines)

end
