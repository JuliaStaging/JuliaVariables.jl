# JuliaVariables

[![Stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://thautwarm.github.io/JuliaVariables.jl/stable)
[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://thautwarm.github.io/JuliaVariables.jl/dev)
[![Build Status](https://travis-ci.com/thautwarm/JuliaVariables.jl.svg?branch=master)](https://travis-ci.com/thautwarm/JuliaVariables.jl)
[![Codecov](https://codecov.io/gh/thautwarm/JuliaVariables.jl/branch/master/graph/badge.svg)](https://codecov.io/gh/thautwarm/JuliaVariables.jl)


```julia
using JuliaVariables
func = solve(:(function f(x)
    let y = x + 1
        y
    end
end))
println(func |> rmlines)

func = solve(:(function f(x)
    y = x + 1
    z -> z + y
end))

println(func |> rmlines)

func = solve(:(function f(x)
    y = x + 1
    let y = y + 1
        (x + y  + z for z in 1:10)
    end
end))
println(func |> rmlines)
```

=>

```julia
[]function (f)(@x)
    let @y = (@global +)(@x, 1)
        @y
    end
end
[]function (f)(@x)
    @cell y = (@global +)(@x, 1)
    [cell y]@z->begin
        (@global +)(@z, @cell y)
    end
end
[]function (f)(@cell x)
    @y = (@global +)(@cell x, 1)
    let @cell y = (@global +)(@cell y, 1)
        [cell y,cell x]((@global +)(@cell x, @cell y, @z) for @z = (@global :)(1, 10))
    end
end
```