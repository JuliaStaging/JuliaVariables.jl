using ParameterisedModule
using MLStyle
using NameResolution
@sig struct S
    scope::Function
end
fatal() = error("fatal")
Scoping() = @structure struct S
    is_real_ctx = true  # functions, etc.
    not_real_ctx = false # let-scope, loop-scope, etc.
    ana_ref = Ref{Analyzer}(top_analyzer())

    function is_rhs end
    function is_lhs end

    function with_scope(ex::Expr, scope::Scope)
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

    function jfor(assigns::Vector{Tuple{Any, Any}}, body::Any)::Tuple{Vector{Symbol}, Scope}
        hd = assigns
        tl = assigns[2:end]
        is_rhs(hd[2])
        with_ctx(not_real_ctx) do
            (is_lhs ⊕ is_local)(hd[1])
            for (lhs, rhs) in tl
                (is_lhs ⊕ is_local)(lhs); is_rhs(rhs)
            end
            scoping(body)
        end
    end

    function jfunc(header::FuncHeader, @nospecialize(body))

    end

    scoping(exp::Expr)::Vector{Symbol} = @match begin
        @match exp begin
            Expr(:for, :($_ = $_)&&assign, body) && Do(assigns = [assign]) ||
            Expr(:for, Expr(:block, assigns...), body) =>
                begin
                    assign_pairs = Tuple{Any, Any}[
                        @when :($lhs = $rhs) = assign begin
                            push!(assign_pairs, (lhs, rhs))
                        @when ::LineNumberNode = assign
                            # do nothing
                        @otherwise
                            fatal()
                        end
                        for assign in assigns
                    ]
                    (syms, scope) = jfor(assign_pairs, body)
                    with_scope(exp, scope)
                    syms
                end
            Expr(:(=), lhs, rhs) => begin
                    header = func_header(lhs)
                    if is_func_header(header)
                        (syms, scope) = jfunc(header, rhs)
                        with_scope(exp, scope)
                        syms
                    else
                        is_lhs(lhs); is_rhs(rhs); Symbol[]
                    end
                end
            Expr(:call, args...) => begin end
        end
    end
end