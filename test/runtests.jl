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

function first_scope_except_top(ex)
    inner = ex.args[2]
    find(ex) = @match ex begin
        Expr(:scoped, scope, inner) => (scope, inner)
        Expr(head, args...) =>
            for each in args
                res = find(each)
                res !== nothing && return res
            end
        _ => nothing
    end
    find(inner)
end

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
    func = solve!(:(function f(x)
        let y = x + 1
            y
        end
    end))
    println(func |> rmlines)

    func = solve!(:(function f(x)
        y = x + 1
        z -> z + y
    end))

    println(func |> rmlines)

    func = solve!(:(function f(x)
        y = x + 1
        let y = y + 1
            for z in 1:10
                x + y + z
            end
        end
    end))
    println(func |> rmlines)

    func = solve!(
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

    func = solve_from_local!(quote
        a -> a + z
    end)
    println(func |> rmlines)

    func = solve_from_local!(quote
    q = a
    function z(x, k=1)
        (x=x, k=k, q=q)
    end
    end)
    println(func |> rmlines)
    # Write your own tests here.

    a = solve!(:(function k(x::T) where T
                (1, T)
              end
    ))

    @test any(x -> x.name == :T, get_fn_scope(a).bounds)

    # a = solve!(:(2 .^ [2, 3]))
    # @test eval(a) == [4, 8]

    a = solve!(:(function z(x, k=1)
                   x + 20 + a + k
               end
    ))

    @test any(x -> x.name == :k, get_fn_scope(a).bounds)

     a = solve_from_local!(quote
            x  = 1
            y  = 2
            .^ = 2
            function z()
                   x .^ y
            end
    end)
    scope = first_scope_except_top(a)[1]
    @test length(scope.freevars) == 2

    a = solve!(:(function z(x, k=1)
                   (k=k, )
               end
    ))

    @test any(x -> x.name == :k, get_fn_scope(a).bounds)

    @test @when :(k=$_, ) = get_fn_body(a).args[end] begin
        true
    @otherwise
        false
    end

    func = solve!(:(function (x)
              z = x + 1
              y -> begin
                  z += 1
                  z
              end
          end))

    println(func |> rmlines)
    @test any(x -> x.name == :z && x.is_mutable, get_fn_scope(func).bounds)

    func = solve!(macroexpand(@__MODULE__, :(@inline function (x)
              z = x + 1
              @inline function (y)
                  z += 1
                  z
              end
          end)))
    println(func |> rmlines)
end

@testset "uninitialized bound variable" begin
        ast = quote
        let x
            x = 5
            function ()
                x = 2
            end
        end
        end |> solve!
        scope = first_scope_except_top(ast)[1]
        @test isempty(scope.bound_inits)
    end

@testset "inplace binary" begin
    ast = quote
        local x
        function ()
            x ^= 5
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    var = scope.freevars[1]
    @test var.name == :x && var.is_mutable
end

@testset "type variables" begin
    ast = quote
        function (::T) where T <: Number
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    var = scope.bounds[1]
    @test var.name == :T

    ast = quote
        function (::T) where {T <: Number, A <: T}
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    # A is not used inside function scope
    @test Set([e.name for e in scope.bounds]) == Set([:T])

    ast = quote
        function (::A) where {T <: Number, T <: A <: GlobalType}
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    @test Set([e.name for e in scope.bounds]) == Set([:T, :A])
end

@testset "default argument is free variables" begin
    ast = quote
        z = 2
        function (x::T = z) where T <: Number
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    var = scope.freevars[1]
    @test var.name == :z
end


@testset "global mark" begin
    ast = quote
        x = 5
        function ()
            global x
            x = 2
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    @test isempty(scope.bounds) && isempty(scope.freevars)
end


@testset "while" begin
    ast = quote
        x = 5
        while cond
            x = 10
        end
    end |> solve!
    scope = first_scope_except_top(ast)[1]
    x = scope.bounds[1]
    @test x.name === :x
    @test x.is_mutable === false
    @test x.is_global === false
end


@testset "let" begin
    ast = quote
        x = 5
        let x
            x = 3
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    @test isempty(scope.freevars)

    ast = quote
        x = 5
        let x = 3
            x
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    @test isempty(scope.freevars)

    ast = quote
        function ()
            x = 5
            let
                y = 1
            end
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    @test scope.bounds[1].name == :x
    @test all(scope.freevars) do var
        var.name !== :y
    end
    @test all(scope.bounds) do var
        var.name !== :y
    end
end

@testset "namedtuple" begin
    ast = quote
        function (c)
            (x = 3, )
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    @test [e.name for e in scope.bounds] == [:c]

    ast = quote
        function (c)
            (x = 3, y=2; z=3)
        end
    end |> solve_from_local!
    scope = first_scope_except_top(ast)[1]
    @test [e.name for e in scope.bounds] == [:c]
end



@testset "broadcast" begin
    ast = quote
        x = 1
        .^ = ^
        y = 2
        function()
            x .^ y
        end
    end |> solve_from_local!
    tp = first_scope_except_top(ast)
    scope = tp[1]
    @test length(scope.freevars) == 2
    @test Set([e.name for e in scope.freevars]) == Set([:x, :y])
    @test @match tp[2].args[end] begin
        :($_ .^ $_) => true
        _ => false
    end
end


@testset "broadcast fusion" begin
    ast = quote
        x = [1, 2]
        function()
            x .= 1
        end
    end |> solve_from_local!
    tp = first_scope_except_top(ast)
    scope = tp[1]
    @test length(scope.freevars) == 1
    @test Set([e.name for e in scope.freevars]) == Set([:x])
    x = scope.freevars[1]
    @test x.is_mutable == false
end

@testset "simplification" begin

    ast = quote
        for i = I, j = J
            let x = 1, y
                c(x) = begin 3 end
                f(x) do
                    1
                end
            end
        end
    end |> rmlines |> simplify_ex

    expec = quote
        for i in I
            for j in J
                let x = 1
                    let y
                        function c(x)
                            3
                        end
                        f(function () 1 end, x)
                    end
                end
            end
        end
    end |> rmlines
    @test string(ast) == string(expec)
end

@testset "no effect" begin
    ast = macroexpand(@__MODULE__(), quote
        function ()
            @label x
            @goto x
        end
    end) |> solve_from_local!
    tp = first_scope_except_top(ast)
    scope = tp[1]
    @test isempty(scope.bounds)
    @test isempty(scope.freevars)

    ast = macroexpand(@__MODULE__(), quote
        @inline function ()
        end
    end) |> solve_from_local!
    tp = first_scope_except_top(ast)
    scope = tp[1]
    @test isempty(scope.bounds)
    @test isempty(scope.freevars)
end

@testset "depwarn" begin
    a = @test_deprecated solve(:(
        function z(x, k = 1)
            x + 20 + a + k
        end
    ))
    @test any(x -> x.name == :k, get_fn_scope(a).bounds)

    a = @test_deprecated solve_from_local(quote
        x  = 1
        y  = 2
        .^ = 2
        function z()
               x .^ y
        end
    end)
    scope = first_scope_except_top(a)[1]
    @test length(scope.freevars) == 2
end

@testset "#23: simplify_ex handling empty let binding" begin
    ex = :(let
        x = 1
    end) |> simplify_ex
    @test Meta.isexpr(ex, :let)
    @test ex.args[1] == Expr(:block)
end