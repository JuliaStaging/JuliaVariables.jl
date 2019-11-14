module JuliaSyntaxUtils
export Unset, FuncArg, FuncHeader, unset, func_arg, func_header, is_func_header
using MLStyle
@generated function field_update(main :: T, field::Val{Field}, value) where {T, Field}
    fields = fieldnames(T)
    quote
        $T($([field !== Field ? :(main.$field) : :value for field in fields]...))
    end
end

function lens_compile(ex, cache, value)
    @when :($a.$(b::Symbol).$(c::Symbol) = $d) = ex begin
        updated =
            Expr(:let,
                Expr(:block, :($cache = $cache.$b), :($value = $d)),
                :($field_update($cache, $(Val(c)), $value)))
        lens_compile(:($a.$b = $updated), cache, value)
    @when :($a.$(b::Symbol) = $c) = ex
        Expr(:let,
            Expr(:block, :($cache = $a), :($value=$c)),
            :($field_update($cache, $(Val(b)), $value)))
    @otherwise
        error("Malformed update notation $ex, expect the form like 'a.b = c'.")
    end
end

function with(ex)
    cache = gensym("cache")
    value = gensym("value")
    lens_compile(ex, cache, value)
end

macro with(ex)
    with(ex) |> esc
end

function with(ex)
    cache = gensym("cache")
    value = gensym("value")
    lens_compile(ex, cache, value)
end

macro with(ex)
    with(ex) |> esc
end

struct Unset end
unset = Unset()

struct FuncArg
    name
    type
    default
end

struct FuncHeader
    name  :: Any
    args  :: Union{Vector{FuncArg}, Unset}
    ret   :: Any
    fresh :: Union{Vector{Any}, Unset}
end

is_func_header(a::FuncHeader) = a.args != unset

function func_arg(@nospecialize(ex))::FuncArg
    @match ex begin
        :($var :: $ty) => @with func_arg(var).type = ty
        :($var = $default) => @with func_arg(var).default = default
        var => FuncArg(var, unset, unset)
    end
end

function func_header(@nospecialize(ex))::FuncHeader
    @match ex begin
        :($hd::$ret) => @with func_header(hd).ret = ret
        :($f($(args...))) => @with func_header(f).args = map(func_arg, args)
        :($f where {$(args...)}) => @with func_header(f).fresh = args
        Expr(:tuple, args...) => FuncHeader(unset, map(func_arg, args), unset, unset)
        f => FuncHeader(f, unset, unset, unset)
    end
end

end