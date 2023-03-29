using Test
using SafeTestsets
using Musica
using Documenter

DocMeta.setdocmeta!(Musica, :DocTestSetup, :(using Musica), recursive=true)

@testset "Musica" begin
  @safetestset "includettu" begin
    include("jokutesti.jl")
  end
end

@testset "doctests" begin
  doctest(Musica, manual=false)
end