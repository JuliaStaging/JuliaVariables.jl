module JuliaVariables
using LegibleLambdas
using MLStyle
using NameResolution

export ScopedVal, Scope, solve

struct ScopedVal
    scope :: Scope
    sym   :: Symbol
end

islinenumbernode(x) = x isa LineNumberNode
rmlines(ex::Expr) = begin
    hd = ex.head
    tl = map(rmlines, filter(!islinenumbernode, ex.args))
    Expr(hd, tl...)
end
rmlines(a) = a

function quick_lambda(ex)
    @when Expr(:call, args...) && if any(==(:_), args) end = ex begin
        @gensym quick_arg
        ex = Expr(:call, Any[arg === :_ ? quick_arg : quick_lambda(arg)
                             for arg in args]...)
        :($LegibleLambdas.@λ($quick_arg -> $ex))
    @when Expr(hd, args...) = ex
        Expr(hd, map(quick_lambda, args)...)
    @otherwise
        ex
    end
end

macro quick_lambda(ex)
    esc(quick_lambda(ex))
end

function func_name(ex)
    @match ex begin
        Expr(:call, f, _...)  => f
        :($a where {$(_...)}) => func_name(a)
        :($a :: $_)           => func_name(a)
        _                     => nothing
    end
end

@active FunSym(sym) begin
    sym === :function
end

@active BroadcastFusing(sym) begin
    s = string(sym)
    endswith(s, "=") && startswith(s, ".")
end

struct CtxFlag
    is_local :: Bool
    is_lhs   :: Bool
end

MLStyle.Record.@as_record

Base.:+(flag :: CtxFlag, desc :: Symbol) =
    @when CtxFlag(is_local=is_local, is_lhs=is_lhs) = flag begin
        @match desc begin
            :global => CtxFlag(false, is_lhs)
            :local  => CtxFlag(true, is_lhs)
            :lhs    => CtxFlag(is_local, true)
            :rhs    => CtxFlag(is_local, false)
        end
    @otherwise
        error("impossible")
    end

CtxFlag() = CtxFlag(true, false)

function solve(ana, ex, ctx_flag::CtxFlag = CtxFlag())
    @match ex begin
        :($a where {$(tps...)}) =>
            @quick_lambda begin
                if !isempty(tps)
                    ana = child_analyzer!(ana)
                end
                tps = map(solve(ana, _, ctx_flag + :lhs), tps)
                a = solve(ana, a, ctx_flag)
                :($a where {$(tps...)})
            end
        Expr(hd && FunSym(is_fn) && (:function || :(=) || :->), a,  b) =>
            begin
                name = func_name(a)
                if name !== nothing
                    enter!(ana, name)
                end
                new_ana = if is_fn || name !== nothing
                    child_analyzer!(ana)
                    ctx_flag = CtxFlag()
                else
                    ana
                end
                a = solve(new_ana, a, ctx_flag + :lhs)
                b = solve(new_ana, b, ctx_flag + :rhs + :local)
                Expr(hd, a, b)
            end
        :($a :: $b) =>
            begin
                a = solve(ana, a, ctx_flag + :local)
                b = solve(ana, b, ctx_flag + :rhs)
                :($a :: $b)
            end
        Expr(hd && (:for || :while), a, b) =>
            begin
                ana = child_analyzer!(ana)
                a   = solve(ana, a, ctx_flag + :lhs)
                b   = solve(ana, b, ctx_flag + :rhs)
                Expr(hd, a, b)
            end
        Expr(:try, attempt, a, blocks...) =>
            @quick_lambda Expr(
                :try,
                solve(child_analyzer!(ana), attempt, ctx_flag + :rhs),
                solve(child_analyzer!(ana), a, ctx_flag + :lhs), # catch as
                map(solve(child_analyzer!(ana), _, ctx_flag + :rhs), blocks)...
            )
        Expr(:let, Expr(:block, binds...), a) =>
            begin
                cur_scope = ana
                binds = map(binds) do each
                    if !isa(each, LineNumberNode)
                        cur_scope = child_analyzer!(cur_scope)
                        solve(cur_scope, each, ctx_flag + :lhs)
                    else
                        each
                    end
                end
                a = solve(cur_scope, a, ctx_flag + :rhs)
                Expr(:let, Expr(:block, binds...), a)
            end
        Expr(:do, call, lam) =>
            begin
                call = solve(ana, call, ctx_flag + :rhs)
                lam = solve(ana, lam, ctx_flag + :rhs)
                Expr(:do, call, lam)
            end
        Expr(:generator, expr, binds...) =>
            @quick_lambda begin
                ana = child_analyzer!(ana)
                binds = map(solve(ana, _, ctx_flag + :lhs), binds)
                expr = solve(ana, expr, ctx_flag + :rhs)
                Expr(:generator, expr, binds...)
            end
        Expr(:filter, cond, binds...) =>
            @quick_lambda begin
                binds = map(solve(ana, _, ctx_flag), binds)
                cond = solve(ana, cond, ctx_flag + :rhs)
                Expr(:filter, cond, binds...)
            end
        Expr(hd && BroadcastFusing(true), a, b) =>
            begin
                a = solve(ana, a, ctx_flag + :lhs)
                b = solve(ana, b, ctx_flag + :rhs + :local)
                Expr(hd, a, b)
            end
        Expr(:local, args...) =>
            @quick_lambda  begin
                args = map(solve(ana, _, ctx_flag + :local), args)
                Expr(:local, args...)
            end
        Expr(:global, args...) =>
            @quick_lambda  begin
                args = map(solve(ana, _, ctx_flag + :global), args)
                Expr(:local, args...)
            end
        Expr(hd, args...) =>
            @quick_lambda begin
                args = map(solve(ana, _, ctx_flag), args)
                Expr(hd, args...)
            end
        sym :: Symbol =>
            begin
                error("NOT IMPL") # TODO
            end
        a => a
    end
end

end