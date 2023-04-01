module CA
using Transducers
using StaticArrays

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

function (dca::Discrete{NS,RD,RuL})(state, generations::Int) where {NS,RD,RuL}
  res = Vector{typeof(state)}(undef, generations)
  res[1] = state
  for i in 2:generations
    state = dca(state)
    res[i] = state
  end
  res
end

function (dca::Discrete{NS,RD,RuL})(state) where {NS,RD,RuL}
  neighborhood_size = RD * 2 + 1
  # state wraps around at the ends
  (state[end-neighborhood_size÷2+1:end], state, state[1:neighborhood_size÷2]) |> Cat() |>
  Consecutive(neighborhood_size, 1) |>
  Map(x -> begin
    idx = undigits(x, NS) + 1
    dca.ruleset[idx]
  end) |>
  collect |>
  similar_type(state)
end

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