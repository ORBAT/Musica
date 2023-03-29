using Transducers

module CA

struct DiscreteCA
  rule::Int
  ruleset::Vector{Int}
  nstates::Int
  radius::Int
end

undigits(d; base=10) = foldr((a, b) -> muladd(base, b, a), d, init=0)

"""
    CA.rule_to_ruleset(rule::Int, nstates::Int = 2, radius::Int = 1)

Return a little-endian vector for the transition rule padded to the max rule length

```jldoctest
CA.rule_to_ruleset(30) # defaults to nstates=2, radius=1

# output
8-element Vector{Int64}:
 0
 1
 1
 1
 1
 0
 0
 0

```
"""
function rule_to_ruleset(rule::Int, nstates::Int=2, radius::Int=1)
  rule_len = nstates^(2 * radius + 1)
  @assert rule ≥ 0 && rule < (nstates^rule_len) "rule number for $(nstates) states must be ≥ 0 and < $(nstates^rule_len), was $(rule)"
  digits(Int, rule, base=nstates, pad=rule_len)
end


end # module CA