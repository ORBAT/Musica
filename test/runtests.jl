using Test
using SafeTestsets

@safetestset "Musica" begin
  include("Musica.jl")
end

@safetestset "CA" begin
  include("CA.jl")
end