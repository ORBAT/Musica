using TestItems, Test

abstract type Neuron{InWidth,OutWidth,NStates} <: Function end

struct CANeuron{Width,NStates} <: Neuron{Width,Width,NStates}
  ca::DiscreteCA
  repeated_ca_fn::Function
  generations::Int

  function CANeuron{Width,NStates}(ca::DiscreteCA{NStates}, gens::Int) where {Width,NStates}
    new(ca, repeated(ca, gens), gens)
  end

end

@inline function (can::CANeuron{W,N})(state::State)::State where {W,N,State<:Row{N}}
  can.repeated_ca_fn(state)
end

@testitem "CA neurons" begin
  ca = DiscreteCA{2}(110)
  row = Row{2,4}([1, 0, 0, 0])
  @test CANeuron{4,2}(ca, 3)(row) == (ca ∘ ca ∘ ca)(row)
  @inferred CANeuron{4,2}(ca, 3)(row)
end