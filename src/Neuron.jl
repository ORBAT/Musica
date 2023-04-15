using TestItems, Test
# module Neuron
# import FromFile: @from

# using ..CA
# struct CAN1{RowWidth,NStates}
#   ca::CA.Discrete
#   generations::Int
#   rowWidth::Int
#   nStates::Int

#   function CAN1{RowWidth,NStates}(ca::CA.Discrete{NStates, Radius, RuleLen}, gens::Int) where {RowWidth, NStates, Radius, RuleLen}
#     new(ca,gens,RowWidth,NStates)
#   end
# end

# CANeuron = CAN1


# end

# @from "CA.jl" import DiscreteCA

struct CAN1{RowWidth,NStates}
  ca::DiscreteCA
  generations::Int
  rowWidth::Int
  nStates::Int

  function CAN1{RowWidth,NStates}(ca::DiscreteCA{NStates, Radius, RuleLen}, gens::Int) where {RowWidth, NStates, Radius, RuleLen}
    new(ca,gens,RowWidth,NStates)
  end
end

CANeuron = CAN1

@testitem "bla" begin
  # using FromFile
  # @from "CA.jl" import DiscreteCA
  @test CANeuron{32,2}(DiscreteCA{2,1}(110), 10)
end