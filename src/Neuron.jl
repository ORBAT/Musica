using TestItems, Test, Lazy
# module Neuron
# import FromFile: @from

# using ..CA
# struct CAN1{RowWidth,NStates}
#   ca::CA.Discrete
#   generations::Int
#   inWidth::Int
#   nStates::Int

#   function CAN1{RowWidth,NStates}(ca::CA.Discrete{NStates, Radius, RuleLen}, gens::Int) where {RowWidth, NStates, Radius, RuleLen}
#     new(ca,gens,RowWidth,NStates)
#   end
# end

# CANeuron = CAN1


# end

# @from "CA.jl" import DiscreteCA

struct CAN1{InWidth,OutWidth,NStates}
  ca::DiscreteCA
  generations::Int
  inWidth::Int
  outWidth::Int
  nStates::Int

  function CAN1{InWidth,OutWidth,NStates}(ca::DiscreteCA{NStates,Radius,RuleLen}, gens::Int) where {InWidth,OutWidth,NStates,Radius,RuleLen}
    new(ca, gens, InWidth, OutWidth, NStates)
  end

  function CAN1{Width,NStates}(ca::DiscreteCA{NStates,Radius,RuleLen}, gens::Int) where {Width,NStates,Radius,RuleLen}
    new{Width,Width,NStates}(ca, gens, Width, Width, NStates)
  end
end

CANeuron = CAN1

function (can::CANeuron{W,N})(state::State)::State where {W,N,State}
  foldl(1:(can.generations); init = state) do acc, _
    can.ca(acc)
  end
end

@testitem "CA neurons" begin
  @test CANeuron{4,2}(DiscreteCA{2,1}(110), 3)([1, 0, 0, 0]) == [1, 0, 1, 1]
end

# struct 