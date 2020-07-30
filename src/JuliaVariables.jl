module JuliaVariables

export Scope, Var
export solve_from_local, solve_from_local!, solve, solve!, simplify_ex

using NameResolution
using Base.Enums
using MLStyle

IdDict = Base.IdDict
Analyzer = NameResolution.Analyzer

include("SimplifyEx.jl")

# auxilliaries
find_line(ex::Expr) = begin
    for e in ex.args
        l = find_line(e)
        l !== nothing && return l
    end
end

find_line(e::LineNumberNode) = e
find_line(_) = nothing
error_ex(sym::Symbol, ex) =
    begin line = find_line(ex)
    locmsg = line === nothing ? "" : "$line: "
    error("$(locmsg)Malformed or non-canonicalized $sym expression")
end


@enum Ctx C_LOCAL C_GLOBAL C_LEXICAL
struct State
    ana::Union{Analyzer, Nothing}
    ctx::Ctx
    bound_inits::Set{Symbol}
end
State(ana::Analyzer, ctx::Ctx) = State(ana, ctx, Set{Symbol}())

mutable struct SymRef
    sym::Symbol
    ana::Union{Nothing, Analyzer}
    as_non_sym::Bool
    # as_non_sym = true : like for a key of namedtuples or argument keywords
end

function Base.show(io::IO, sym::SymRef)
    flag = ""
    if sym.ana === nothing
        flag *= "wild "
    end
    if sym.as_non_sym
        flag *= "nonsym "
    end
    print(io, "$(flag)$(sym.sym)")
end

SymRef(sym::Symbol, ana::Union{Nothing, Analyzer}) = SymRef(sym, ana, false)

struct Var
    name::Symbol
    is_mutable::Bool
    is_shared::Bool
    is_global::Bool
end

function Base.show(io::IO, var::Var)
    var.is_global && return print(io, "@global ", var.name)
    mut = var.is_mutable ? "mut " : ""
    var.is_shared && return print(io,  "$(mut)@shared ", var.name)
    print(io,  "$(mut)@local ", var.name)
end

macro _symref_func(N, n)
    quote
        $__source__
        function $N(symref::SymRef)
            $n(symref.ana, symref.sym)
        end
    end |> esc
end


@_symref_func ENTER! enter!
@_symref_func REQUIRE! require!
@_symref_func IS_LOCAL! is_local!
@_symref_func IS_GLOBAL! is_global!

const INPLACE_BIN_OP = (
    :(+=), :(-=), :(*=), :(/=), :(//=), :(%=), :(&=), :(|=), :(\=), :(^=))

is_broadcast_sym(sym) = begin
    s = string(sym)
    startswith(s, ".") && Base.isoperator(Symbol(s[1:end]))
end

is_broadcast_fusing(sym) = begin
    s = string(sym)
    endswith(s, "=") && startswith(s, ".")
end

function no_ana(ex)
    @match ex begin
        # inline
        Expr(:meta, _...)          ||
        # @label, @goto
        Expr(:symboliclabel, _...) ||
        Expr(:symbolicgoto, _...)  ||
        # @inbounds
        Expr(:inbounds, _...)      ||
        # @generated
        Expr(:generated, _...)     ||
        # @boundscheck
        Expr(:boundscheck, _...)   ||
        # @isdefined
        Expr(:isdefined, _...)     ||
        # @locals
        Expr(:locals) => true
        _ => false
    end
end

"""Process expressions with returning their scope.
The `solve!` function can only accept ASTs that
satifies following conditions:
- It's a *simplified* expression, which means `JuliaVariables.simplify_ex`
  will have no effects on the expression. You can check the very concise code
  of `JuliaVariables.simplify_ex` to understand the simplification rules.
- No macros included in the expression, as we don't know how much a macro
  could change the code.
"""
function solve!(ast; toplevel=true)
    S = Ref(State(top_analyzer(), C_LEXICAL, Set{Symbol}()))
    ScopeInfo = IdDict{Expr,Any}()
    PHYSICAL = true
    PSEUDO = false
    IS_BOUND_INIT = Ref(false)

    @nospecialize
    function LHS(ex)
        syms = rule(ex)
        st = S[]
        st.ctx ===
            C_LOCAL ?
            IS_LOCAL!.(syms) :
        st.ctx ===
            C_GLOBAL ?
            IS_GLOBAL!.(syms) :
            nothing
        ENTER!.(syms)
        REQUIRE!.(syms)
        IS_BOUND_INIT[] && return for sym in syms
            sym.as_non_sym = true
            push!(st.bound_inits, sym.sym)
        end
    end

    function RHS(ex)
        syms = rule(ex)
        REQUIRE!.(syms)
    end

    function LOCAL()
        s = S[]
        S[] = State(s.ana, C_LOCAL, s.bound_inits)
        nothing
    end

    function LOCAL(ex)
        syms = rule(ex)
        IS_LOCAL!.(syms)
        REQUIRE!.(syms)
    end

    function GLOBAL()
        s = S[]
        S[] = State(s.ana, C_GLOBAL, s.bound_inits)
        nothing
    end

    function GLOBAL(ex)
        syms = rule(ex)
        IS_GLOBAL!.(syms)
        REQUIRE!.(syms)
    end

    function CHILD(st::State, p::Bool)
        ana = st.ana
        new_ana = child_analyzer!(ana, p)
        State(new_ana, C_LEXICAL)
    end

    function WITH_STATE(f::Function)
        S_ = S[]
        try
            f()
        finally
            S[] = S_
        end
    end

    function WITH_STATE(f::Function, st::State)
        S_ = S[]
        S[] = st
        try
            f()
        finally
            S[] = S_
        end
    end

    function LOCAL_LHS(st, ex)
        WITH_STATE(st) do
            LOCAL()
            ns = IS_BOUND_INIT[]
            try
                IS_BOUND_INIT[] = true
                LHS(ex)
            finally
                IS_BOUND_INIT[] = ns
            end
        end
    end

    LHS(st, ex) = WITH_STATE(st) do; LHS(ex) end
    RHS(st, ex) = WITH_STATE(st) do; RHS(ex) end
    LOCAL(st, ex) = WITH_STATE(st) do; LOCAL(ex) end
    GLOBAL(st, ex) = WITH_STATE(st) do; GLOBAL(ex) end
    LOCAL_LHS(ex) = LOCAL_LHS(S[], ex)

    @specialize

    function IS_SCOPED(st::State, ex::Expr)
        ScopeInfo[ex] =(st.ana.solved.bounds, st.ana.solved.freevars, st.bound_inits)
    end

    rule(_) = SymRef[]
    rule(sym::Symbol) =
        error("An immutable Symbol cannot be analyzed. Transform them to SymRefs.")
    rule(sym::SymRef) = begin
        sym.ana = S[].ana; SymRef[sym]
    end
    rule(ex::Expr)::Vector{SymRef} =
        @when (_ && if no_ana(ex) end) = nothing begin
            SymRef[]
        @when Expr(:let, :($a = $b), body) = ex
            S₀ = S[]
            S₁ = CHILD(S₀, PSEUDO)
            RHS(S₀, b)
            LOCAL_LHS(S₁, a)
            RHS(S₁, body)
            S[] = S₀
            IS_SCOPED(S₁, body)
            SymRef[]

        @when Expr(:let, a::SymRef, body) = ex
            S₀ = S[]
            S₁ = CHILD(S₀, PSEUDO)
            LOCAL(S₁, a)
            RHS(S₁, body)
            IS_SCOPED(S₁, body)
            S[] = S₀
            SymRef[]

        @when Expr(:let, Expr(:block), body) = ex
            S₀ = S[]
            S₁ = CHILD(S₀, PSEUDO)
            RHS(S₁, body)
            IS_SCOPED(S₁, body)
            S[] = S₀
            SymRef[]

        @when Expr(:let, seq, body) = ex
            error_ex(:let, seq)

# assign is canonicalized, thus cannot be a function
        @when Expr(:(=), lhs, rhs) = ex
            @when Expr(:call, _...) = lhs begin error_ex(:(=), ex) end
            LHS(lhs)
            RHS(rhs)
            SymRef[]

# broadcast fusing
        @when Expr(hd && if is_broadcast_fusing(hd) end, lhs, rhs) = ex
            RHS(lhs)
            RHS(rhs)
            SymRef[]

# addition assignment, https://github.com/thautwarm/JuliaVariables.jl/issues/6
        @when Expr(hd && if hd in INPLACE_BIN_OP end, lhs, rhs) = ex
            LHS(lhs)
            RHS(rhs)
            SymRef[]

# broadcasting symbols
        @when (
            Expr(:call, f :: SymRef, args...) &&
                if length(args) in (1, 2) && is_broadcast_sym(f.sym)
                end
            ) = ex
            f.as_non_sym = true
            RHS.(args)
            Symbol[]
# namedtuple
# https://github.com/thautwarm/GG.jl/issues/8
        @when Expr(:tuple, elts...) = ex
            syms = SymRef[]
            for elt in elts
                sym_ex = @when :($a = $b) = elt begin
                    a isa SymRef || error("invalid namedtuple")
                    a.as_non_sym = true
                    b
                @otherwise
                    elt
                end
                append!(syms, rule(sym_ex))
            end
            syms

        @when Expr(:where, t, tps...) = ex
            S₁ = CHILD(S[], PSEUDO)
            for tp in tps
                @match tp begin
                :($a >: $b) || :($a <: $b) => begin LOCAL_LHS(S₁, a); RHS(S₁, b) end
                :($a >: $b >: $c) ||
                :($a <: $b <: $c) => begin RHS(S₁, a); LOCAL_LHS(S₁, b); RHS(S₁, c) end
                ::SymRef => begin LOCAL_LHS(S₁, tp) end
                _ => error_ex(:where, ex)
                end
            end
            RHS(S[], t)
            SymRef[]

        @when Expr(:kw, k, v) = ex
            k isa SymRef || error("invalid keyword argument")
            k.as_non_sym = true
            rule(v)

        @when Expr(:for, :($i = $I), body) = ex
            S₀ = S[]
            S₁ = CHILD(S₀, PSEUDO)
            IS_SCOPED(S₁, body)
            RHS(S₀, I)
            LOCAL_LHS(S₁, i)
            RHS(S₁, body)
            SymRef[]

        @when Expr(:while, cond, body) = ex
            S₀ = S[]
            S₁ = CHILD(S₀, PSEUDO)
            IS_SCOPED(S₁, body)
            RHS(S₀, cond)
            RHS(S₁, body)
            SymRef[]

        @when Expr(:local, args...) = ex
            WITH_STATE() do
                LOCAL()
                for arg in args
                    LOCAL(arg)
                end
            end
            SymRef[]

        @when Expr(:global, args...) = ex
            WITH_STATE() do
                GLOBAL()
                for arg in args
                    GLOBAL(arg)
                end
            end
            SymRef[]


        @when Expr(:function, header, body) = ex
            left = header
            S₀ = S[]
            S₁ = CHILD(S₀, PSEUDO)
            S₂ = CHILD(S₁, PHYSICAL)
            IS_SCOPED(S₂, body)

            # check type parameters
            @when :($left_ where {$(freshes...)}) = left begin
                S[] = S₁
                for decl in freshes
                        @match decl begin
                        :($a >: $b) || :($a <: $b) => begin LOCAL_LHS(a); LOCAL_LHS(S₂, a); RHS(b) end
                        :($a >: $b >: $c) ||
                        :($a <: $b <: $c) => begin RHS(a); LOCAL_LHS(b); LOCAL_LHS(S₂, b); RHS(c) end
                        ::SymRef => begin LOCAL_LHS(decl); LOCAL_LHS(S₂, decl) end
                        _ => error_ex(:where, ex)
                    end
                end
                left = left_;nothing
            end

            # check return type
            @when :($left_::$t) = left begin
                RHS(S₁, t)
                left = left_;nothing
            end

            # check function name
            args = @match left begin
                Expr(:call, f, args...) => begin LHS(S₀, f); args end
                Expr(:tuple, args...)   => args
                # declaration
                ::Symbol => []
                _ => error_ex(:function, ex)
            end

            # check args
            function visit_arg(arg)
                @nospecialize arg
                @when (:($arg_ = $default) || Expr(:kw, arg_, default)) = arg begin
                    RHS(S₂, default)
                    arg = arg_
                end
                @when :($arg_::$t) = arg begin
                    RHS(S₁, t)
                    arg = arg_
                end
                LOCAL_LHS(S₂, arg)
            end
            for arg in args
                @when Expr(:parameters, kwargs...) = arg begin
                    foreach(visit_arg, kwargs)
                @otherwise
                    visit_arg(arg)
                end
            end
            RHS(S₂, body)
            S[] = S₀
            SymRef[]

        @when Expr(_, args...) = ex
            syms = SymRef[]
            for each in args
                append!(syms, rule(each))
            end
            syms
        end

    function local_var_to_var(var::LocalVar)::Var
        Var(var.sym, var.is_mutable[], var.is_shared[], false)
    end

    function to_symref(ex::Expr)
        args = ex.args
        for i = 1:length(args)
            args[i] = to_symref(args[i])
        end
        ex
    end

    function to_symref(s::Symbol)
        SymRef(s, nothing)
    end

    to_symref(@nospecialize(l)) = l

    function from_symref(ex::Expr)
        args = ex.args
        for i = 1:length(args)
            args[i] = from_symref(args[i])
        end
        haskey(ScopeInfo, ex) && return begin
            triple = ScopeInfo[ex]
            scope_info = (
                bounds = Var[local_var_to_var(v) for (_, v) = triple[1]],
                freevars = Var[local_var_to_var(v) for (_, v) = triple[2]],
                bound_inits = Symbol[triple[3]...]
            )
            Expr(:scoped, scope_info, ex)
        end
        ex
    end

    function from_symref(s::SymRef)
        s.as_non_sym && return s.sym
        s.ana === nothing && return Var(s.sym, true, true, true)
        var = s.ana.solved[s.sym]
        var isa Symbol && return Var(var, true, true, true)
        local_var_to_var(var)
    end

    from_symref(s::Symbol) =
        error("An immutable Symbol cannot be analyzed. Transform them to SymRefs.")

    from_symref(l) = l

    function transform(@nospecialize(ex))
        ex = to_symref(ex)
        if toplevel
            GLOBAL()
        end
        IS_SCOPED(S[], ex)
        rule(ex)
        ana = S[].ana
        run_analyzer(ana)
        from_symref(ex)
    end

    transform(ast)
end # module struct

solve_from_local!(@nospecialize(ex)) = solve!(ex; toplevel=false)

_depwarn(sym) = Base.depwarn(
    "`$sym(ex)` is deprecated in JuliaVariables 0.2.x. " *
    "Please use `$(sym)!(ex)` instead.  `$sym(ex)`, which currently mutates `ex` " *
    "in-place, will be re-introduced in 0.3 as a non-mutating variant.",
    sym,
)

function solve(@nospecialize(ex))
    _depwarn(:solve)
    solve!(ex)
end

function solve_from_local(@nospecialize(ex))
    _depwarn(:solve_from_local)
    solve_from_local!(ex)
end

end # module
