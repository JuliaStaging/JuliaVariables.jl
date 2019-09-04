module JuliaVariables
using LegibleLambdas
using MLStyle
using NameResolution

export ScopedVal, Scope, solve

struct ScopedVal
    scope :: Scope
    sym   :: Symbol
end

Base.show(io::IO, scopedval::ScopedVal) =
    Base.print(io, string(objectid(scopedval.scope), base=60), "@", scopedval.sym)

islinenumbernode(x) = x isa LineNumberNode
rmlines(ex::Expr) = begin
    hd = ex.head
    tl = map(rmlines, filter(!islinenumbernode, ex.args))
    Expr(hd, tl...)
end
rmlines(a) = a

function quick_lambda(ex)
    @when Expr(:call, args...) && if any(==(:_), args) end = ex begin
        quick_arg = gensym("quick_arg")
        λ = gensym("λ")
        args = Any[arg === :_ ? quick_arg : quick_lambda(arg)
                   for arg in args]
        ex = Expr(:call, args...)
        :(function $λ($quick_arg) $ex end)
    @when Expr(hd, args...) = ex
        Expr(hd, map(quick_lambda, args)...)
    @otherwise
        ex
    end
end

macro quick_lambda(ex)
    esc(quick_lambda(ex))
end

function with_fname(cont, ex)
    @match ex begin
        Expr(:call, f, args...)  => Expr(:call, cont(f), args...)
        :($a where {$(args...)}) => :($(with_fname(cont, a)) where {$(args...)})
        :($a :: $t)              => :($(with_fname(cont, a)) :: $t)
        a                        => a
    end
end

is_func_sym(sym) = sym === :function

is_broadcast_fusing(sym) = begin
    s = string(sym)
    endswith(s, "=") && startswith(s, ".")
end

is_rhs_sym(sym) = begin
    (sym in Symbol[:ref, :.])
end

@data ScopeDesc begin
    Force(is_local :: Bool)
    Lexical()
end

struct CtxFlag
    default_scope :: ScopeDesc
    is_lhs        :: Bool
end
MLStyle.Record.@as_record CtxFlag

Base.@pure Base.:+(flag :: CtxFlag, desc :: Symbol) =
    @when CtxFlag(default_scope=default_scope, is_lhs=is_lhs) = flag begin
        @match desc begin
            :lexical => CtxFlag(Lexical(), is_lhs)
            :global  => CtxFlag(Force(false), is_lhs)
            :local   => CtxFlag(Force(true), is_lhs)
            :lhs     => CtxFlag(default_scope, true)
            :rhs     => CtxFlag(default_scope, false)
        end
    @otherwise
        error("impossible")
    end

CtxFlag() = CtxFlag(Lexical(), false)

function solve(ana, sym :: Symbol, ctx_flag::CtxFlag)
    @when Force(is_local) = ctx_flag begin
        if is_local
            is_local!(ana, sym)
        else
            is_global!(ana, sym)
        end
    end
    if ctx_flag.is_lhs
        enter!(ana, sym)
    else
        require!(ana, sym)
    end
    ScopedVal(ana.solved.x, sym)
end

function solve(ana, ex, ctx_flag::CtxFlag = CtxFlag())
    @match ex begin
        Expr(hd && if hd in (:function, :(=), :->) end, a,  b) =>
            begin
                is_fn = is_func_sym(hd)
                a = with_fname(a) do name
                    is_fn = true
                    !(name isa Symbol) && return name
                    solve(ana, name, ctx_flag + :lhs)
                end
                ana = if is_fn
                    child_analyzer!(ana)
                else
                    ana
                end
                a = solve(ana, a, ctx_flag + :lhs + :local)
                b = solve(ana, b, CtxFlag())
                Expr(hd, a, b)
            end
        Expr(hd && if hd in (:for, :while) end, a, b) =>
            begin ctx_flag = CtxFlag()
                ana      = child_analyzer!(ana)
                a   = solve(ana, a, ctx_flag + :lhs + :local)
                b   = solve(ana, b, ctx_flag)
                Expr(hd, a, b)
            end
        Expr(:try, attempt, a, blocks...) =>
            @quick_lambda begin ctx_flag = CtxFlag()
                attempt = solve(child_analyzer!(ana), attempt, ctx_flag)
                a       = solve(child_analyzer!(ana), a, ctx_flag + :lhs) # catch exc
                blocks  = map(solve(child_analyzer!(ana), _, ctx_flag), blocks)
                Expr(:try, attempt, a, blocks...)
            end
        Expr(:let, Expr(:block, binds...) || bind && Do(binds = [bind]), a) =>
            begin ctx_flag = CtxFlag() + :lhs + :local
                @info :let "???"
                cur_scope = ana
                binds = map(binds) do each
                    if !isa(each, LineNumberNode)
                        cur_scope = child_analyzer!(cur_scope)
                        solve(cur_scope, each, ctx_flag)
                    else
                        each
                    end
                end
                a = solve(cur_scope, a, CtxFlag())
                Expr(:let, Expr(:block, binds...), a)
            end
        Expr(:do, call, lam) =>
            begin
                ctx_flag = CtxFlag()
                call = solve(ana, call, ctx_flag)
                lam = solve(ana, lam, ctx_flag)
                Expr(:do, call, lam)
            end
        Expr(:generator, expr, binds...) =>
            @quick_lambda begin ctx_flag = CtxFlag()
                ana = child_analyzer!(ana)
                binds = map(solve(ana, _, ctx_flag + :lhs + :local), binds)
                expr = solve(ana, expr, ctx_flag)
                Expr(:generator, expr, binds...)
            end
        Expr(:filter, cond, binds...) =>
            @quick_lambda begin
                binds = map(solve(ana, _, ctx_flag), binds)
                cond = solve(ana, cond, ctx_flag)
                Expr(:filter, cond, binds...)
            end
        Expr(hd && if is_broadcast_fusing(hd) end, a, b) =>
            begin
                a = solve(ana, a, ctx_flag + :lhs)
                b = solve(ana, b, ctx_flag + :rhs + :lexical)
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
# non-scoped constructs
        :($a where {$(tps...)}) =>
            @quick_lambda begin
                if !ctx_flag.is_lhs && !isempty(tps)
                    ana = child_analyzer!(ana)
                    ctx_flag = CtxFlag()
                    tps = map(solve(ana, _, ctx_flag + :lhs), tps)
                end
                a = solve(ana, a, ctx_flag)
                :($a where {$(tps...)})
            end
        :($a :: $b) =>
            begin
                a = solve(ana, a, ctx_flag)
                b = solve(ana, b, CtxFlag())
                :($a :: $b)
            end
        Expr(hd, args...) =>
            @quick_lambda begin
                if is_rhs_sym(hd)
                    ctx_flag += :rhs
                end
                args = map(solve(ana, _, ctx_flag), args)
                Expr(hd, args...)
            end
        a => a
    end
end

function solve(ex)
    ana = top_analyzer()
    ana, solve(ana, ex)
end

end # module
