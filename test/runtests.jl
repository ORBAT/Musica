using Test
using SafeTestsets
using Musica

@testset "Blerg" begin
  @safetestset "includettu" begin
    include("jokutesti.jl")
  end
end