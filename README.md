# JuliaVariables

[![Stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://thautwarm.github.io/JuliaVariables.jl/stable)
[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://thautwarm.github.io/JuliaVariables.jl/dev)
[![Build Status](https://travis-ci.com/thautwarm/JuliaVariables.jl.svg?branch=master)](https://travis-ci.com/thautwarm/JuliaVariables.jl)
[![Codecov](https://codecov.io/gh/thautwarm/JuliaVariables.jl/branch/master/graph/badge.svg)](https://codecov.io/gh/thautwarm/JuliaVariables.jl)


About
=============

The `solve` function will solve the scopes of a **simplified** Julia expression.

- The variables(`Symbol`) are transformed to `Var`:
    ```julia
    struct Var
        name       :: Symbol
        is_mutable :: Bool
        is_shared  :: Bool
        is_global  :: Bool
    end
    ```
- Some expressions will be wrapped within `Expr(:scoped, (bounds=..., freevars=..., bound_inits=...), inner_expression)`.

Example
==============

`solve` & `solve_from_local`
-----------------------------

```julia
julia> using MLStyle

julia> unwrap_scoped(ex) =
           @match ex begin
               Expr(:scoped, _, a) => unwrap_scoped(a)
               Expr(head, args...) => Expr(head, map(unwrap_scoped, args)...)
               a => a
           end
unwrap_scoped (generic function with 1 method)

julia> quote
           x = 1
           function (a)
               x = 1
           end
       end |>  solve_from_local |> rmlines |> unwrap_scoped
quote
    mut @shared x = 1
    function (a,)
        mut @shared x = 1
    end
end


julia> quote
           x = 1
           function ()
               x = 1
           end
       end |>  solve |> rmlines
:($(Expr(:scoped, (bounds = Var[], freevars = Var[], bound_inits = Symbol[]), quote
    @global x = 1
    function ()
        $(Expr(:scoped, (bounds = Var[@local x], freevars = Var[], bound_inits = Symbol[]), quote
    @local x = 1
end))
    end
end)))


julia> quote
           x = 1
           function ()
               x = 1
           end
       end |>  solve_from_local |> rmlines
:($(Expr(:scoped, (bounds = Var[mut @shared x], freevars = Var[], bound_inits = Symbol[]), quote
    mut @shared x = 1
    function ()
        $(Expr(:scoped, (bounds = Var[], freevars = Var[mut @shared x], bound_inits = Symbol[]), quote
    mut @shared x = 1
end))
    end
end)))
```

`simplify_ex`
-------------------

Not all expressions can be accepted as the input of `solve` or `solve_from_local`, thus we provide such a
handy API to apply conversions from almost arbitrary
expressions to the *simplified* expressions.

```julia
julia> quote
          function f(x)
               for i in I, j in J
                   let x = 1, y
                       () -> 2
                   end
               end
               f(x) = 2
          end
       end |> rmlines |> simplify_ex
quote
    function f(x)
        for i = I
            for j = J
                let x = 1
                    let y
                        function ()
                            2
                        end
                    end
                end
            end
        end
        function f(x)
            2
        end
    end
end
```

The reason why we don't couple this API with `solve` is, we need to let user aware that there exists destructive operations for expressing the scope information, for instance, it's impossible to inject
scope information to `for i in I, j in J; body end`, because
the AST shape of it is

```julia
Expr(:for,
    Expr(:block,
        :(i = I),
        :(j = J),
    ),
    Expr(:block, body)
)
```

`Expr(:block, body)` is actually in the sub-scope of
that of `:(j = J)`, and `:(j=J)`'s scope in inherited from that of `:(i=I)`, which ruins the handy use(especially the top-down tree visiting) of scoped expressions.

Not only due to the uselessness of scoping the messy ASTs like `for i in I, j in J; body end`, the analyses for them are also much more ugly to implement than those of the *simplified* expressions. Finally, I give up doing this.

If you have understand the above concerns and made
sure it's safe to return a restructured expression after injecting scope information, you can compose
`simplify_ex` and `solve` to gain a more handy API:

```julia
mysolve = solve ∘ simplify_ex
mysolve_from_local = solve_from_local ∘ simplify_ex
```