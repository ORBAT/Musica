push!(LOAD_PATH,"../src/")

using Documenter, ImplicitArrays

const pages = [
    "Home" => "index.md"
]

makedocs(
    modules   = [ImplicitArrays],
    clean     = true,
    doctest   = true,
    linkcheck = true,
    checkdocs = :all,
    pages     = pages,
    format    = Documenter.HTML(),
    sitename  = "ImplicitArrays.jl",
    repo      = "https://github.com/tkemmer/ImplicitArrays.jl/blob/master{path}"
)

deploydocs(;
    repo = "github.com/tkemmer/ImplicitArrays.jl.git",
    devbranch = "master"
)
