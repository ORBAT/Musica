module CA
using Transducers
using StaticArrays
using ComputedFieldTypes


# struct DiscreteCA{NStates<:Int,Radius<:Int}
#   rule::Int
#   ruleset::SVector{NStates^(2 * Radius + 1),Int}
#   nstates::Int
#   radius::Int

#   function DiscreteCA{NStates,Radius}(rule::Int) where {NStates<:Int,Radius<:Int}
#     new(rule, _rule_to_ruleset(rule, Val{NStates}(), Val{Radius}()), NStates, Radius)
#   end
# end

struct DC3{NStates,Radius,RuleLen}
  rule::Int
  ruleset::SVector{RuleLen,Int}
  nstates::Int
  radius::Int

  function DC3{NStates,Radius,RuleLen}(rule::Int) where {NStates,Radius,RuleLen}
    new(rule, _rule_to_ruleset_s(rule, Val{NStates}(), Val{Radius}(), Val{RuleLen}()), NStates, Radius)
  end
end

function DC3{NStates,Radius}(rule::Int) where {NStates,Radius}
  DC3{NStates,Radius,NStates^(2 * Radius + 1)}(rule)
end

Discrete = DC3

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
  rule_len = nstates^(2 * radius + 1)
  _rule_to_ruleset_s(rule, Val(nstates), Val(radius), Val(rule_len))
end


function _rule_to_ruleset_s(rule::Int, ::Val{NStates}, ::Val{Radius}, ::Val{RuleLen}) where {NStates,Radius,RuleLen}
  @assert rule ≥ 0 && rule < (NStates^RuleLen) "rule number for $(NStates) states must be ≥ 0 and < $(NStates^RuleLen), was $(rule)"
  SVector{RuleLen}(digits(Int, rule, base=NStates, pad=RuleLen))
end

end # module CA