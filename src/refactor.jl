using ParameterisedModule
using NameResolution
using Base.Enums
using MLStyle
@use UppercaseCapturing
IdDict = Base.IdDict
Analyzer = NameResolution.Analyzer

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
        loc_msg === nothing ? "" : "$line :"
        error("$(locmsg)Malformed or non-canonicalized $sym expression")
    end


@enum Ctx C_LOCAL C_GLOBAL C_LEXICAL
struct State
    ana :: Analyzer
    ctx :: Ctx
    bound_inits::Set{Symbol}
end
State(ana::Analyzer, ctx::Ctx) = State(ana, ctx, Set{Symbol}())

mutable struct SymRef
    sym        :: Symbol
    scope      :: Union{Nothing, Scope}
    as_non_sym :: Bool
    # as_non_sym = true : like for a key of namedtuples or argument keywords
end

SymRef(sym::Symbol, scope::Union{Nothing, Scope}) = SymRef(sym, scope, false)

@sig struct Scoper
    S :: Ref{State}
    ScopeInfo :: IdDict{Any, Any}
    rule :: Function
end

macro _symref_func(N, n)
    quote
        $__source__
        function $N(ana::Analyzer, symref::SymRef)
            symref.scope = ana.solved
            $n(ana, symref.sym)
        end
    end |> esc
end

@_symref_func ENTER! enter!
@_symref_func REQUIRE! require!
@_symref_func IS_LOCAL! is_local!
@_symref_func IS_GLOBAL! is_global!

scoper() = @structure struct Scoper
    S = Ref(State(top_analyzer(), C_LEXICAL, Set{Symbol}()))
    ScopeInfo = IdDict{Any, Any}()
    PHYSICAL = true
    PSEUDO = false
    IS_BOUND_INIT = Ref(false)

    @nospecialize
    function LHS(st::State, ex)
        syms = rule(ex)
        st.ctx === C_LOCAL ?
            IS_LOCAL!.([st.ana], syms) :
        st.ctx === C_GLOBAL ?
            IS_GLOBAL!.([st.ana], syms) : nothing
        ENTER!.([st.ana], syms)
        IS_BOUND_INIT[] && return for sym in syms
            sym.as_non_sym = true
            push!(st.bound_inits, sym.sym)
        end
        # REQUIRE!.([st.ana], syms)
    end

    function RHS(st::State, ex)
        syms = rule(ex)
        REQUIRE!.([st.ana], syms)
    end

    function LOCAL()
        s = S[]
        S[] = State(s.ana, C_LOCAL)
        nothing
    end

    function LOCAL(st::State, ex)
        syms = rule(ex)
        IS_LOCAL!.([st.ana], syms)
    end

    function GLOBAL()
        s = S[]
        S[] = State(s.ana, C_GLOBAL)
        nothing
    end

    function GLOBAL(st::State, ex)
        syms = rule(ex)
        IS_GLOBAL!.([st.ana], syms)
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

    function LOCAL_LHS(st::State, ex)
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

    LHS(ex) = LHS(S[], ex)
    RHS(ex) = RHS(S[], ex)
    LOCAL(ex) = LOCAL(S[], ex)
    GLOBAL(ex) = GLOBAL(S[], ex)
    CHILD(p) = CHILD(S[], ex)
    LOCAL_LHS(ex) = LOCAL_LHS(S[], ex)
    @specialize

    rule(_) = SymRef[]
    rule(sym::Symbol) =
        error("An immutable Symbol cannot be analyzed. Transform them to SymRefs.")
    rule(sym::SymRef) = SymRef[sym]
    rule(ex::Expr)::Vector{SymRef} =
        @when Expr(:let, :($a = $b), body) = ex begin
            S₀ = S[]
            S₁ = CHILD(S₀, PSEUDO)
            RHS(S₀, b)
            LOCAL_LHS(S₁, a)
            RHS(S₁, body)
            S[] = S₀
            SymRef[]

        @when Expr(:let, a::Symbol, body) = ex
            S₀ = S[]
            S₁ = CHILD(S₀, PSEUDO)
            LOCAL_LHS(S₁, a)
            RHS(S₁, body)
            S[] = S₀; SymRef[]

        @when Expr(:let, seq, body) = ex

            error_ex(:let, seq)

        @when Expr(:function, header, body) = ex
            left = header
            S₀ = S[]
            S₁ = CHILD(S₀, PSEUDO)
            S₂ = CHILD(S₁, PHYSICAL)
            ScopeInfo[ex] = (S₀.ana.solved, S₀.bound_inits)

            # check type parameters
            @when :($left_ where {$(freshes...)}) = left begin
                S[] = S₁
                for decl in freshes
                    @match decl begin
                        :($a >: $b) || :($a <: $b) => begin LOCAL_LHS(a); RHS(b) end
                        :($a >: $b >: $c) ||
                        :($a <: $b <: $c) => begin RHS(a); LOCAL_LHS(b); RHS(c) end
                        _ => error_ex(:where, ex)
                    end
                end
                left = left_;nothing
            end

            # check return type
            @when :($left_ :: $t) = left begin
                RHS(S₁ , t)
                left=left_;nothing
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
                @when :($arg_ = $default) ||
                    Expr(:kw, arg_, default) = arg begin
                    RHS(S₂, default)
                    arg = arg_
                end
                @when :($arg_ :: $t) = arg begin
                    RHS(S₁, default)
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

        @when Expr(:(=), lhs, rhs) = ex
            # assign is canonicalized, thus cannot be a function
            @when Expr(:call, _...) = lhs begin error_ex(:(=), ex) end
            LHS(lhs)
            RHS(rhs)
            SymRef[]

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

        @when Expr(:kw, k, v) = ex
            k isa SymRef || error("invalid keyword argument")
            k.as_non_sym = true
            rule(v)

        @when Expr(:for, :($i = $I), block) = ex

            S₀ = S[]
            S₁ = CHILD(S₀, pseudo)
            RHS(S₀, I)
            LOCAL_LHS(S₁, i)
            RHS(S₁, block)
            SymRef[]

        @when Expr(:while, cond, body) = ex
            S₀ = S[]
            S₁ = CHILD(S₀, pseudo)
            RHS(S₀, cond)
            RHS(S₁, body)
            SymRef[]

        @when Expr(:local, args...) = ex
            WITH_STATE() do
                LOCAL()
                for arg in args
                    syms = rule(arg)
                    LOCAL(syms)
                    RHS(syms)
                end
            end

        @when Expr(:global, args...) = ex
            WITH_STATE() do
                GLOBAL()
                for arg in args
                    syms = rule(arg)
                    GLOBAL(syms)
                    RHS(syms)
                end
            end
        @when Expr(_, args...) = ex
            syms = SymRef[]
            for each in args
                append!(syms, rule(each))
            end
            syms
        end
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
    ex
end

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

function from_symref(s::SymRef)
    s.as_non_sym && return s.sym
    var = s.scope[s.sym]
    var isa Symbol && return Var(var, true, true, true)
    Var(var.sym, var.is_mutable[], var.is_shared[], false)
end

from_symref(s::Symbol) =
    error("An immutable Symbol cannot be analyzed. Transform them to SymRefs.")
from_symref(l) = l

ss = scoper()

ex = quote
    y = 1
    function f(x)
        y + x
    end
end

ex = to_symref(ex)
ss.rule(ex)
ana = ss.S[].ana
run_analyzer(ana)
ex = from_symref(ex)

println(ex)
