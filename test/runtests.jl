using TestItems
@testitem "doctests" begin
  using Documenter
  using Musica  
  DocMeta.setdocmeta!(Musica, :DocTestSetup, :(using Musica), recursive=true)
  doctest(Musica, manual=false)
end

@testitem "CA" begin
  include("CA.jl")
end