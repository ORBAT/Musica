module CA
using Transducers, StaticArrays, TestItems, Test


Row{L} = SVector{L,Int}

struct DS2{NStates,Radius,RuleLen}
  rule::Int
  ruleset::SVector{RuleLen,Int}
  nstates::Int
  radius::Int

  function DS2{NStates,Radius,RuleLen}(rule::Int) where {NStates,Radius,RuleLen}
    @assert rule ≥ 0 && rule < (NStates^RuleLen) "rule number for $(NStates) states must be ≥ 0 and < $(NStates^RuleLen), was $(rule)"
    @assert RuleLen == NStates^(2 * Radius + 1) "RuleLen must be NStates^(2 * Radius + 1)"
    new(rule, rule_to_ruleset(rule, Val{NStates}(), Val{Radius}()), NStates, Radius)
  end
end

Discrete = DS2

function Discrete{NStates,Radius}(rule::Int) where {NStates,Radius}
  Discrete{NStates,Radius,NStates^(2 * Radius + 1)}(rule)
end

@testitem "CA initialization" begin
  @test_throws AssertionError CA.Discrete{2,1}(256)
  @test_throws AssertionError CA.Discrete{2,1}(-1)
  @test_throws AssertionError CA.Discrete{3,1}(3^27)
  @test CA.rule_to_ruleset(22, 3) == [[1, 1, 2]; zeros(Int, 27 - 3)]
end

# function (dca::Discrete{NS,RD,RuL})(state, generations::Int) where {NS,RD,RuL}
#   res = Vector{typeof(state)}(undef, generations)
#   res[1] = state
#   for i in 2:generations
#     state = dca(state)
#     res[i] = state
#   end
#   res
# end

"""
* `NS` = `NStates`
* `RD` = `Radius`

**HOX HOX** kokeillu vähän kaikkea mutta tän return type jostain syystä vaan tahtoo olla `any` jos statea ei tyypitä
"""
function (dca::Discrete{NS,RD,RuL})(state::T)::T where {NS,RD,RuL,T}
  neighborhood_size = RD * 2 + 1


  # state wraps around at the ends
  (state[end-neighborhood_size÷2+1:end], state, state[1:neighborhood_size÷2]) |> Cat() |>
  Consecutive(neighborhood_size, 1) |> # slice into windows of neighborhood_size, 1 step at a time
  Map(x -> begin
    # turn each neighborhood x into a number, use that to index into the ruleset to get the result
    idx = undigits(x, NS) + 1
    dca.ruleset[idx]
  end) |>
  collect |>
  similar_type(T)
end

@testitem "evolution" begin
  using StaticArrays
  state = @SVector [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ca = CA.Discrete{2,1}(110)

  @test ca(state) == [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  @test @inferred(ca(state)) broken=true
end;

"""
    CA.undigits(d, base=2)

Treat d as a little-endian vector of digits in `base` and return the base-10 representation.

```jldoctest
julia> CA.undigits([0, 1, 1, 1, 1, 0, 0, 0])
30

julia> CA.undigits(CA.rule_to_ruleset(22, 3), 3)
22
```
"""
undigits(d, base=2) = foldr((digit, acc) -> muladd(base, acc, digit), d, init=0)

"""
    CA.rule_to_ruleset(rule::Int, nstates::Int = 2, radius::Int = 1)

Return a little-endian vector for the transition rule padded to the max rule length

```jldoctest
julia> x = CA.rule_to_ruleset(30);

julia> show(x)
[0, 1, 1, 1, 1, 0, 0, 0]

```
"""
function rule_to_ruleset(rule::Int, nstates::Int=2, radius::Int=1)
  rule_to_ruleset(rule, Val(nstates), Val(radius))
end

function rule_to_ruleset(rule::Int, ::Val{NStates}, ::Val{Radius}) where {NStates,Radius}
  RuleLen = NStates^(2 * Radius + 1)
  SVector{RuleLen,Int}(digits(Int, rule, base=NStates, pad=RuleLen))
end

end # module CA