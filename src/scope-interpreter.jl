using Base.Enums


scoper = @structure struct Interpreter
    Repr = Vector{Symbol}
    function normal(args::Vararg{Repr})
        vcat(args...)
    end
    jcall = normal
    function jfor(assigns, block)
        Meta.isexpr(assigns, :block) && return begin
            # for i in I, j in J, ...;
        end
        # for i in I;
    end
    function jleaf(e)
        @match e begin
            ::Symbol => Symbol[e]
            _ => Symbol[]
        end
    end
end