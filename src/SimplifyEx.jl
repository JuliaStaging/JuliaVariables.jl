using MLStyle

_wrap_block(ex::Expr) = ex
_wrap_block(o) = Expr(:block, o)
_simplify_block(ex) = _wrap_block(simplify_ex(ex))


function simplify_ex(ex::Expr)
    @match ex begin
        Expr(:for, Expr(:block, assigns...), body) =>
            foldr(assigns, init=_simplify_block(body)) do ass, last
                Expr(:for, simplify_ex(ass), last)
            end
        Expr(:let, Expr(:block), body) =>
            Expr(:let, Expr(:block), _simplify_block(body))
        Expr(:let, Expr(:block, assigns...), body) =>
            foldr(assigns, init=_simplify_block(body)) do ass, last
                Expr(:let, simplify_ex(ass), last)
            end
        Expr(:(=), lhs && Expr(:call, _...), rhs) =>
            Expr(:function, simplify_ex(lhs), simplify_ex(rhs))
        Expr(:->, lhs && Expr(:tuple, _...), rhs) =>
            Expr(:function, simplify_ex(lhs), simplify_ex(rhs))
        Expr(:(->), lhs, rhs) =>
            Expr(:function, Expr(:tuple, simplify_ex(lhs)), simplify_ex(rhs))
        Expr(:do, Expr(:call, f, args...), lam) =>
            Expr(:call, simplify_ex(f), simplify_ex(lam), map(simplify_ex, args)...)
        Expr(head, args...) =>
            Expr(head, map(simplify_ex, args)...)
    end
end

simplify_ex(s) = s