using ComputedFieldTypes, StaticArrays

# HOX: DiscreteCA on omassa filussaan, koska muuten Revise menee särki @computed:in kanssa. Jos samassa
# filussa määrittelee useamman structin joista ees yks on @computed, niin Revise herjaa aina vaan invalid
# redefinitionista vaikkei DiscreteCA:han olis koskenut tikullakaan

@computed struct DiscreteCA{NStates,Radius,RuleLen} <: Function
  rule::UInt
  rule_lookup::SVector{RuleLen,NStates == 2 ? Bool : Int}

  function DiscreteCA{NStates,Radius,RuleLen}(rule) where {NStates,Radius,RuleLen}
    @assert 0 ≤ rule < (NStates^RuleLen)
    _r = convert(UInt, rule)
    @assert RuleLen == NStates^(2 * Radius + 1) "RuleLen must be NStates^(2 * Radius + 1)"
    new(rule, rule_to_rule_lookup(_r, NStates, Radius))
  end
end

export DiscreteCA
