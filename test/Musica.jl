using TestItems, Test
@testitem "doctests" begin
  using Documenter
  DocMeta.setdocmeta!(Musica, :DocTestSetup, :(using Musica), recursive=true)
  doctest(Musica, manual=false)
end