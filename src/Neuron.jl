using TestItems, Test

abstract type Neuron{NStates,InWidth,OutWidth} <: Function end

struct CANeuron{NStates,Width} <: Neuron{NStates,Width,Width}
  ca::DiscreteCA
  repeated_ca_fn::Function
  generations::Int

  function CANeuron{NStates,Width}(ca::DiscreteCA{NStates}, gens::Int) where {NStates,Width}
    new(ca, repeated(ca, gens), gens)
  end

end

function (can::CANeuron{N,W})(state::State)::State where {N,W,State<:Row{N}}
  can.repeated_ca_fn(state)
end

@testitem "CA neurons" begin
  ca = DiscreteCA{2}(110)
  row = Row{2,4}([1, 0, 0, 0])
  @test CANeuron{2,4}(ca, 3)(row) == (ca ∘ ca ∘ ca)(row)
  @inferred CANeuron{2,4}(ca, 3)(row)
end