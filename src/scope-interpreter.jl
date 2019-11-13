using Base.Enums
using NameResolution
Analyzer = NameResolution.Analyzer

struct Thunk{F}
    f      :: F
    result :: Ref{Union{Some, Nothing}}
end

function force(t::Thunk)
    res = t.result
    value = res[]
    if !isnothing(value)
        value
    end
    value = t.f()
    res[] = Some(value)
    value
end

macro thunk(ex)
    @match ex begin
        Expr(:function, head, body) =>
            Expr(:function, head, quote
                $Thunk($Ref{$Union{$Some, $Nothing}}(nothing)) do
                    $body
                end
            end)
        _ => error("malformed thunk!")
    end
end

scoper = @structure struct Interpreter
    Repr = Thunk
    force_cur_ctx = force
    is_real_ctx = true  # functions, etc.
    not_real_ctx = false # let-scope, loop-scope, etc.
    ana_ref = Ref{Analyzer}(top_analyzer())

    is_rhs!(s::Symbol) = require!(ana_ref[], s)
    is_rhs!(xs::Vector{Symbol}) = foreach(is_rhs!, xs)
    is_rhs!(a::Repr) = is_rhs!(force_cur_ctx(a))

    is_lhs!(s::Symbol) = begin ana = ana_ref[]
            enter!(ana, s)
            require!(ana, s)
        end
    is_lhs!(xs::Vector{Symbol}) = foreach(is_lhs!, xs)
    is_lhs!(a::Repr) = is_lhs!(force_cur_ctx(a))

    """
    make an expression as a scoped expression, with
    side effects
    """
    function with_scope!(ex::Expr, scope::Scope)
        inner = Expr(ex.head, ex.args...)
        ex.head = :scope
        ex.args = Any[scope, inner]
    end

    function with_ctx(f::Function, real_ctx::Bool)
        ana = ana_ref[]
        try
            new_ana = child_analyzer(ana, real_ctx)
            ana_ref[] = new_ana
            f(), new_ana.solved
        finally
            ana_ref[] = ana
        end
    end

    @thunk function normal(ex::Any, args::Vararg{Repr})
        vcat(map(force_cur_ctx, args)...)
    end

    jcall = normal
    jtuple = normal
    jvect = normal
    jand = normal
    jor = normal

    @thunk function jfor(ex::Expr, assign, block)
        assigns = Meta.isexpr(assign, :block) ?
            # for i in I, j in J, ...;
            # only I is evaluated in outer ctx
            assigns = assign.args :
            [assign]
        ass_pairs = map(assigns) do ass
            @match ass begin
                Expr(:(=), lhs, rhs) => (lhs, rhs)
                _ => error("invalid julia syntax $assign")
            end
        end
        is_rhs!(ass_pairs[1][2])

        syms, scope = with_ctx(false) do
            is_lhs!(ass_pairs[1][1])
            for i = 2:length(ass_pairs)
                (lhs, rhs) = ass_pairs[i]
                is_lhs!(lhs)
                is_rhs!(rhs)
            end
            force_cur_ctx(block)
        end
        with_scope!(ex, scope)
        syms
    end
    @thunk function jassign(_::Expr, )

    @thunk function jleaf(@nospecialize(e))
        @match e begin
            ::Symbol => Symbol[e]
            _ => Symbol[]
        end
    end
end