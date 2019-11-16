# Specification of Julia Scoping Rule

`S` indicates the current scope.
Some terminologies(as well as interfaces provided in NameResolution.jl) :
- `LHS`: left-hide-side
- `RHS`: right-hide-side
- `pseudo scope`: a scope but does not introduce free variables in its parent scope. I don't know how to call it actually, `pseudo scope` is a tentative name.
- `LOCAL`: to mark a symbol as **local**, instead of resolving it automatically
- `GLOBAL`: to mark a symbol as **global**, instead of resolving it automatically

## For Loop

```julia
for i = I, j in J
    body
end
```

`i` is LHS in in `S/for1`, `I` is RHS in `S`.

`j` is LHS in `S/for1/for2`, `J` is RHS in `S/for1`.

`body` is RHS in `S/for1/for2`.


## Standalone Assignments

```julia
$f = a
```

If `$f` is a function calling expression, it's treated as `function $f; a end` . See [Function Definition](#Function Definition).

Otherwise, all symbols(except heads of expressions) of `$f` are LHS in `S`, `a` is RHS in `S`.

## Functions

```julia
function f(x::A{T}=default_value) where T
    body
end
```

- `f` is LHS in `S`(however the function name should be marked for further analysis, e.g., self recursions).

There's a *pseudo* scope `S/mk-type-params`,

- `T` in `where T` is LHS in `S/mk-type-params`.

The requirement of a symbol in argument type annotations is from the scope `S/mk-type-params`.

Say,
- `T` in `f(x::A{T}=value)` is RHS in `S/mk-type-params`, and
- `A` is RHS in `S/mk-type-params`(though we know `A` is from `S`, pseudo scope doesn't result in free variables).

The function execution has the scope `S/mk-type-params/inner` and,
- `x` is LHS in `S/mk-type-params/inner`,
- `default_value` is RHS in `S/mk-type-params/inner`,
- `body` is RHS in `S/mk-type-params/inner`


Except for
- `Expr(:function, ::Symbol, Expr(:block, _...))` is a declaration

## Let-Bindings

```julia
let a = b
    c
end
```

`S/let` is a pseudo scope.

- `b` is RHS in `S`
- `a` is LHS in `S/let`
- `c` is RHS in `S/let`
