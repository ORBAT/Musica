using Test
using Documenter
using Musica

DocMeta.setdocmeta!(Musica, :DocTestSetup, :(using Musica), recursive=true)


@test Musica.fuck == 1
@test 1 == 5 broken = true

doctest(Musica, manual=false)