using Test
using Documenter
using Musica

DocMeta.setdocmeta!(Musica, :DocTestSetup, :(using Musica), recursive=true)

doctest(Musica, manual=false)