using TestItems, Test

abstract type Neuron{InWidth,OutWidth,NStates} end

struct CAN1{Width,NStates} <: Neuron{Width,Width,NStates}
  ca::DiscreteCA
  generations::Int
  width::Int
  nStates::Int

  function CAN1{Width,NStates}(ca::DiscreteCA{NStates,Radius,RuleLen}, gens::Int) where {Width,NStates,Radius,RuleLen}
    new(ca, gens, Width, NStates)
  end

end

CANeuron = CAN1

function (can::CANeuron{W,N})(state::State)::State where {W,N,State}
  # foldl takes a fn (acc, x). (can.ca ∘ _left) is (acc,_) -> can.ca(acc)
  # this is basically just can.ca composed with itself can.generation times (can.ca ∘ can.ca ∘ ... )
  foldl((can.ca ∘ _left), 1:can.generations; init=state)
end

@testitem "CA neurons" begin
  ca = DiscreteCA{2,1}(110)
  @test CANeuron{4,2}(ca, 3)([1, 0, 0, 0]) == (ca ∘ ca ∘ ca)([1, 0, 0, 0])
  @inferred CANeuron{4,2}(ca, 3)([1, 0, 0, 0])
end