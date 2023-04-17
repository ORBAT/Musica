using Transducers, StaticArrays, TestItems, Test

struct DiscreteCA{NStates,Radius,RuleLen}
  rule::Int
  ruleset::SVector{RuleLen,Int}
  nstates::Int
  radius::Int

  function DiscreteCA{NStates,Radius,RuleLen}(rule::Int) where {NStates,Radius,RuleLen}
    @assert 0 ≤ rule < (NStates^RuleLen) "rule number for $(NStates) states must be ≥ 0 and < $(NStates^RuleLen), was $(rule)"
    @assert RuleLen == NStates^(2 * Radius + 1) "RuleLen must be NStates^(2 * Radius + 1)"
    new(rule, rule_to_ruleset(rule, Val{NStates}(), Val{Radius}()), NStates, Radius)
  end
end

function DiscreteCA{NStates,Radius}(rule::Int) where {NStates,Radius}
  DiscreteCA{NStates,Radius,NStates^(2 * Radius + 1)}(rule)
end

@testitem "CA initialization" begin
  @test_throws AssertionError DiscreteCA{2,1}(256)
  @test_throws AssertionError DiscreteCA{2,1}(-1)
  @test_throws AssertionError DiscreteCA{3,1}(3^27)
end

"""
* `NS` = `NStates`
* `RD` = `Radius`

**HOX HOX** kokeillu vähän kaikkea mutta tän return type jostain syystä vaan tahtoo olla `any` jos statea ei tyypitä
"""
function (dca::DiscreteCA{NS,RD,RuL})(state::State)::State where {NS,RD,RuL,State}
  new_state = similar(State, axes(state))
  neighborhood_size = RD * 2 + 1
  
  # transducer that:
  # – slices into windows of neighborhood_size, 1 step at a time
  # – turns each neighborhood x into a number, uses that to index into the ruleset to get the result
  # – enumerates the result into tuples of (idx, value)
  xf = Consecutive(neighborhood_size, 1) |> 
  Map(x -> dca.ruleset[undigits(x, NS) + 1]) |>
  Enumerate()
  
  # state wraps around at the ends
  wrapped_state = (state[end-neighborhood_size÷2+1:end], state, state[1:neighborhood_size÷2]) |> Cat()
  # run wrapped_state through xf, fold it into new_state 
  foldl(xf, wrapped_state; init = new_state) do acc, (idx, a) 
    acc[idx] = a
    acc
  end
end

@testitem "evolution" begin
  using StaticArrays
  state = @SVector [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ca = DiscreteCA{2,1}(110)

  @test ca(state) == [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  @inferred(ca(state))
end

"""
    undigits(d, base=2)

Treat d as a little-endian vector of digits in `base` and return the base-10 representation.

```jldoctest
julia> Musica.undigits([0, 1, 1, 1, 1, 0, 0, 0])
30

julia> Musica.undigits(Musica.rule_to_ruleset(22, 3), 3)
22
```
"""
undigits(d, base=2) = foldr((digit, acc) -> muladd(base, acc, digit), d, init=0)

"""
    rule_to_ruleset(rule::Int, nstates::Int = 2, radius::Int = 1)

Return a little-endian vector for the transition rule padded to the max rule length

```jldoctest
julia> x = Musica.rule_to_ruleset(30);

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

@testitem "Rule number to ruleset" begin
  @test Musica.rule_to_ruleset(22, 3) == [[1, 1, 2]; zeros(Int, 27 - 3)]
end