module JuliaVariables
import LegibleLambdas
using MLStyle
using NameResolution

export Scope, ScopedVar, ScopedFunc, ScopedGenerator
export solve_from_local, solve
const DEBUG = false
@static if DEBUG
macro logger(call)
    @when :($f($ana, $(args...))) = call begin
        :($f($ana, $(args...)) = begin
            println($(QuoteNode(f)),'(', $string($objectid($ana), base=62), ",", $(args...), ')')
            $NameResolution.$f($ana, $(args...))
        end)
    end
end
@logger child_analyzer!(ana, is_physical)
@logger enter!(ana, sym)
@logger require!(ana, sym)
@logger is_local!(ana, sym)
@logger is_global!(ana, sym)
end
@generated function field_update(main :: T, field::Val{Field}, value) where {T, Field}
    fields = fieldnames(T)
    quote
        $T($([field !== Field ? :(main.$field) : :value for field in fields]...))
    end
end

macro with(main, field::Symbol, value)
    :($field_update($main, $(Val(field)), $value)) |> esc
end

struct ScopedVar
    scope :: Scope
    sym   :: Symbol
end

struct ScopedFunc
    scope :: Scope
    func  :: Expr
end

struct ScopedGenerator
    scope :: Scope
    gen  :: Expr
end

function var_repr(var :: LocalVar)
    r = ""
    if var.is_mutable.x
        r *= "mut "
    end
    if var.is_shared.x
        r *= "cell "
    end
    r * string(var.sym)
end
function var_repr(var :: GlobalVar)
    "global $var"
end

function Base.show(io::IO, scopedvar::ScopedVar)
    scope = scopedvar.scope
    sym = scopedvar.sym
    if isempty(scope.bounds) && isempty(scope.freevars)
        Base.print(io, sym)
        return
    end
    var = var_repr(scope[sym])
    Base.print(io, "@", var)
end

function Base.show(io::IO, o::ScopedFunc)
    scope = o.scope
    func = o.func
    Base.print(io, "[", join(map(var_repr, values(scope.freevars) |> collect), ",") , "]", func)
end

function Base.show(io::IO, o::ScopedGenerator)
    scope = o.scope
    gen = o.gen
    Base.print(io, "[", join(map(var_repr, values(scope.freevars) |> collect), ",") , "]", gen)
end


islinenumbernode(x) = x isa LineNumberNode
rmlines(ex::Expr) = begin
    hd = ex.head
    tl = map(rmlines, filter(!islinenumbernode, ex.args))
    Expr(hd, tl...)
end

rmlines(ex::ScopedFunc) = begin
    func = ex.func |> rmlines
    @with ex func func
end

rmlines(ex::ScopedGenerator) = begin
    gen = ex.gen |> rmlines
    @with ex gen gen
end

rmlines(a) = a

function quick_lambda(ex)
    @when Expr(:call, args...) && if any(==(:_), args) end = ex begin
        quick_arg = gensym("quick_arg")
        λ = gensym("λ")
        args = Any[arg === :_ ? quick_arg : quick_lambda(arg)
                   for arg in args]
        ex = Expr(:call, args...)
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
    @when Force(is_local) = ctx_flag.default_scope begin
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
    ScopedVar(ana.solved, sym)
end

function solve(ana, ex, ctx_flag::CtxFlag = CtxFlag())
    @match ex begin
# give up analysing macrocall expressions.
        Expr(:macrocall, _...) => ex
# scoped constructs
        Expr(hd && if hd in (:function, :(=), :->) end, a,  b) =>
            begin
                is_fn = is_func_sym(hd)
                a = with_fname(a) do name
                    is_fn = true
                    !(name isa Symbol) && return name
                    solve(ana, name, ctx_flag + :lhs)
                end
                is_fn = is_fn || hd !== :(=)
                ana = if is_fn
                    child_analyzer!(ana, true)
                else
                    ana
                end
                a = solve(ana, a, ctx_flag + :lhs + :local)
                b = solve(ana, b, CtxFlag())
                func = Expr(hd, a, b)
                is_fn ? ScopedFunc(ana.solved, func) : func
            end
        Expr(hd && if hd in (:for, :while) end, a, b) =>
            begin ctx_flag = CtxFlag()
                ana = child_analyzer!(ana, false)
                a   = solve(ana, a, ctx_flag + :lhs + :local)
                b   = solve(ana, b, ctx_flag)
                Expr(hd, a, b)
            end
        Expr(:try, attempt, a, blocks...) =>
            @quick_lambda begin ctx_flag = CtxFlag()
                attempt = solve(child_analyzer!(ana, false), attempt, ctx_flag)
                a       = solve(child_analyzer!(ana, false), a, ctx_flag + :lhs) # catch exc
                blocks  = map(solve(child_analyzer!(ana, false), _, ctx_flag), blocks)
                Expr(:try, attempt, a, blocks...)
            end
        Expr(:let, Expr(:block, binds...) || bind && Do(binds = [bind]), a) =>
            begin ctx_flag = CtxFlag() + :lhs + :local
                cur_scope = ana
                binds = map(binds) do each
                    if !isa(each, LineNumberNode)
                        cur_scope = child_analyzer!(cur_scope, false)
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
                ana = child_analyzer!(ana, true)
                binds = map(solve(ana, _, ctx_flag + :lhs + :local), binds)
                expr = solve(ana, expr, ctx_flag)
                ScopedGenerator(ana.solved, Expr(:generator, expr, binds...))
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
                    ana = child_analyzer!(ana, false)
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
        Expr(hd && if hd in (:module, :baremodule) end, args...) =>
           @quick_lambda Expr(hd, map(solve(ana, _, ctx_flag), args)...)
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
    ex = solve(ana, ex)
    anas = [(@with child parent nothing) for child in ana.children]
    foreach(run_analyzer, anas)
    ex
end

function solve_from_local(ex)
    ana = top_analyzer()
    ex = solve(ana, ex)
    run_analyzer(ana)
    ex
end

end # module