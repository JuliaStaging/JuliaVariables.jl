using Documenter, JuliaVariables

makedocs(;
    modules=[JuliaVariables],
    format=Documenter.HTML(),
    pages=[
        "Home" => "index.md",
    ],
    repo="https://github.com/thautwarm/JuliaVariables.jl/blob/{commit}{path}#L{line}",
    sitename="JuliaVariables.jl",
    authors="thautwarm",
    assets=String[],
)

deploydocs(;
    repo="github.com/thautwarm/JuliaVariables.jl",
)
