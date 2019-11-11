using ParameterisedModule
using MLStyle
@sig struct Interpreter
    struct Repr end
    jcall :: Function
    jfor :: Function
    jwhile :: Function
    jtry :: Function
    jlet :: Function
    jdo :: Function
    jlocal :: Function
    jglobal :: Function
    jwhere :: Function
    jmodule :: Function
    jtuple :: Function
    jvect :: Function
    jassign :: Function
    jquote :: Function
    jsplice :: Function
    jand :: Function
    jor  :: Function
    jconst :: Function

    jline :: Function
    jleaf :: Function

end

const dispatch = Dict(
    :const => :jconst,
    :call => :jcall,
    :for => :jfor,
    :while => :jwhile,
    :try => :jtry,
    :let => :jlet,
    :do => :jdo,
    :local => :jlocal,
    :global => :jglobal,
    :where => :jwhere,
    :module => :jmodule,
    :vect => :jvect,
    :(=) => :jassign,
    :&& => :jand,
    :|| => :jor,
    :quote => :jquote,
    :$ => :jsplice
)


i::Interpreter ++ s::Symbol = getpropety(i, dispatch[s])

function tagless_initial(ex::Any)
    ex isa LineNumberNode && return
        function line(i::Interpreter)
            getpropety(i, :jline)(ex)
        end
    ex isa Expr && return
        if haskey(dispatch, ex.hd)
            let args = map(tagless_initial, ex.args),
                hd = ex.hd
                function expr(i::Interpreter)
                    getpropety(i, dispatch[s])(args...)
                end
            end
        else
            error("没实现")
        end
    function leaf(i::Interpreter)
        getpropety(i, :jleaf)(ex)
    end
end
