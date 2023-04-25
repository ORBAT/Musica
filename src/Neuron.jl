using TestItems, Test

abstract type Neuron{NStates,InWidth,OutWidth} <: Function end

struct CANeuron{NStates,Width} <: Neuron{NStates,Width,Width}
  ca::DiscreteCA
  repeated_ca_fn::Function
  generations::Int

  function CANeuron{NStates,Width}(ca::DiscreteCA{NStates}, gens::Int) where {NStates,Width}
    if gens < 0
      gens = 1
    end
    new(ca, repeated(ca, gens), gens)
  end

end

function (can::CANeuron{N,W})(state::State)::State where {N,W,State<:Row{N,W}}
  can.repeated_ca_fn(state)
end

function parse_n_bits(bv::BitVector, n)::Tuple{BitVector,Int}
  (bv |> Drop(n) |> collect, undigits(bv |> Take(n) |> collect))
end

const _bits_for_generation = 6

parser_bits_required(::Type{<:CANeuron{2}}) = _bits_for_generation + parser_bits_required(DiscreteCA{2})

function parser(::Type{<:CANeuron{2,W}}) where {W}
  function p(bv::BitVector)::Tuple{BitVector,CANeuron{2,W}}
    bitsleft, generations = parse_n_bits(bv, _bits_for_generation)
    bitsleft, ca = parser(DiscreteCA{2})(bitsleft)
    (bitsleft, CANeuron{2,W}(ca, generations))
  end
end

@testitem "CA neurons" begin
  ca = DiscreteCA{2}(110)
  row = Row{2,4}([1, 0, 0, 0])
  @test CANeuron{2,4}(ca, 3)(row) == (ca ∘ ca ∘ ca)(row)
  @inferred CANeuron{2,4}(ca, 3)(row)
end

@testitem "CANeuron parsing" begin
  n_generations = 12
  rule = 110
  gen_bits = digits(n_generations; base=2, pad=6)
  ca_bits = digits(rule; base=2, pad=8)
  full_bits = BitVector(vcat(gen_bits, ca_bits))

  extra_bits = BitVector(vcat(gen_bits, ca_bits, ca_bits))

  p = Musica.parser(CANeuron{2,8})

  @test p(full_bits) == (Bool[], CANeuron{2,8}(DiscreteCA{2}(110), n_generations))
  @test p(BitVector(gen_bits)) == (Bool[], CANeuron{2,8}(DiscreteCA{2}(0), n_generations))
  @test p(extra_bits) == (BitVector(ca_bits), CANeuron{2,8}(DiscreteCA{2}(110), n_generations))
end
end