module ParameterisedModule
using MLStyle

export @sig, @structure, @open, mk_signature, mk_structure, open_module, module_get, module_types, module_values

abstract type MLModule end

extract_tvar(var :: Union{Symbol, Expr})::Symbol =
    @match var begin
        :($a <: $_) => a
        :($a >: $_) => a
        :($_ >: $a >: $_) => a
        :($_ <: $a <: $_) => a
        a::Symbol         => a
    end

function module_get end
function module_values end
function module_types end

function mk_signature(__source__, __module__, ex)
    @when :(struct $modtype; $(decls...) end) = ex begin
        typedecls = Symbol[]
        valsigs = Tuple{Symbol, Any}[]
        line = __source__
        (modn, modps) = @match modtype begin
            :($modn{$(modps...)}) => (modn, modps)
            modn::Symbol => (modn, [])
            a => error("invalid signature name $a")
        end
        foreach(decls) do decl
            @match decl begin
                :(struct $(n::Symbol); $(_...) end) => push!(typedecls,  n)
                :($x :: $t) =>
                    if x isa Symbol
                        push!(valsigs, (x, t))
                    else
                        error("invalid value declaration $x, expect a Symbol.")
                    end
                l::LineNumberNode => (line = l)
                a => error("invalid declaration $a")
            end
        end

        valns   = map(x -> x[1], valsigs)
        valts   = map(x->x[2], valsigs)
        ex_valts = Expr(:curly, :Tuple, valts...)
        use_modps = map(extract_tvar, modps)

        val_type_conflicts = [n in typedecls for n in valns]

        any(val_type_conflicts) &&
            error("Name conflicts: names $val_type_conflicts in both types and values.")

        @gensym Values
        @gensym values

        fieldgetter = Expr[]

        append!(fieldgetter, [
            :(
                $ParameterisedModule.module_get($values :: $modn, ::Val{$(QuoteNode(n))}) =
                    getfield($values, $(QuoteNode(values)))[$i]
            )
            for (i, n) in enumerate(valns)
        ])

        append!(fieldgetter, [
            :(
                $ParameterisedModule.module_get(
                    $values :: $modn{$(use_modps...),
                                     $(typedecls...)},
                    $Values::Val{$(QuoteNode(n))}) where {$(use_modps...), $(typedecls...)} = $n
            )
            for n in typedecls
        ])
        quote
            $__source__

            struct $modn{
                        $(modps...),
                        $(typedecls...),
                        $Values <: $ex_valts
                    } <: $MLModule
                $values :: $Values
            end

            $ParameterisedModule.module_types(::Type{$modn}) = $(Tuple(typedecls))
            $ParameterisedModule.module_values(::Type{$modn}) = $(Tuple(valns))

            Base.getproperty($values :: $modn, $Values::Symbol) =
                $ParameterisedModule.module_get($values, Val{$Values}())

            $(fieldgetter...)
        end
    @otherwise
        error("invalid signature")
    end
end

function mk_structure(__source__, __module__, ex)
    @when :(struct $modtype; $(decls...) end) = ex begin
        line = __source__
        (modn, modps) = @match modtype begin
            :($modn{$(modps...)}) => (modn, modps)
            modn::Symbol => (modn, [])
            a => error("invalid signature name $a")
        end
        mod = __module__.eval(modn)
        type_ns = module_types(mod)
        value_ns = module_values(mod)
        body = Any[]
        for decl in decls
            @match decl begin
                Expr(:abstract, _...) || Expr(:struct, _...) => __module__.eval(decl)
                _ => push!(body, decl)
            end
        end

        vals = Expr(:tuple, value_ns...)
        @gensym val
        push!(body,
            :(
                let $val = $vals
                    $mod{$(modps...), $(type_ns...), typeof($val)}($val)
                end
            ))
        Expr(:let, Expr(:block), Expr(:block, body...))
    @otherwise
        error("invalid structure")
    end
end

macro sig(ex)
    __module__.eval(mk_signature(__source__, __module__, ex))
end

macro structure(ex)
    esc(mk_structure(__source__, __module__, ex))
end

function open_module(::Type{M}, m) where M <: MLModule
    value_ns = module_values(M)
    type_ns = module_types(M)
    ret = Expr[]
    for each in value_ns
        push!(ret, :($each = $m.$each))
    end
    for each in type_ns
        push!(ret, :($each = $m.$each))
    end
    ret
end

macro open(mtype, m)
    esc(Expr(:block, open_module(__module__.eval(mtype), m)...))
end

macro open(mtype, m, inner)
    esc(
        Expr(:let,
            Expr(:block, open_module(__module__.eval(mtype), m)...),
            inner
        ))
end

end # module
