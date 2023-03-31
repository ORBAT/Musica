using Test
using Documenter
using Musica

@test_throws AssertionError CA.Discrete{2,1}(256)
@test_throws AssertionError CA.Discrete{2,1}(-1)
@test_throws AssertionError CA.Discrete{3,1}(3^27)
@test CA.rule_to_ruleset(22, 3) == [[1, 1, 2]; zeros(Int, 27 - 3)]

@testset "evolution" begin
  
  state = @SVector [1, 0, 0, 0, 0, 0, 0]
  ca = CA.Discrete{2,1}(110)

  @test ca(state) == [1, 1, 0, 0, 0, 0, 0]
end