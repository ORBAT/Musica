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

## 

function Base.show(io::IO, can::CANeuron{NS,Width}) where {NS,Width}
  print(io, "CANeuron($(can.ca), width=$Width, gens=$(can.generations))")
end

function Base.show(io::IO, ::MIME"text/plain", can::CANeuron{NS,Width}) where {NS,Width}
  print(io, "CANeuron($(can.ca), width=$Width, gens=$(can.generations))")
end


function (can::CANeuron{N,W})(state::State)::State where {N,W,State<:Row{N,W}}
  can.repeated_ca_fn(state)
end

function parse_n_bits(bits::T, n)::Tuple{BitVector,Int} where {T<:AbstractArray}
  (bits |> Drop(n) |> collect, undigits(bits |> Take(n) |> collect))
end

const default_bits_per_generation = 5

parser_bits_required(::Type{<:CANeuron{2}}; bits_per_gen::Type{Val{_bits_per_generation}}=Val{default_bits_per_generation}, restkw...) where {_bits_per_generation} = _bits_per_generation + parser_bits_required(DiscreteCA{2}; restkw...)

function parser(::Type{<:CANeuron{2,W}}; bits_per_gen::Type{Val{_bits_per_generation}}=Val{default_bits_per_generation}) where {W,_bits_per_generation}
  function p(bits::T)::Tuple{BitVector,CANeuron{2,W}} where {T<:AbstractArray}
    bitsleft, generations = parse_n_bits(bits, _bits_per_generation)
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
  const bits_per_gen = 5
  gen_bits = digits(n_generations; base=2, pad=bits_per_gen)
  ca_bits = digits(rule; base=2, pad=8)
  full_bits = BitVector(vcat(gen_bits, ca_bits))

  extra_bits = BitVector(vcat(gen_bits, ca_bits, ca_bits))

  p = Musica.parser(CANeuron{2,8}; bits_per_gen=Val{bits_per_gen})

  @test p(full_bits) == (Bool[], CANeuron{2,8}(DiscreteCA{2}(110), n_generations))
  @test p(BitVector(gen_bits)) == (Bool[], CANeuron{2,8}(DiscreteCA{2}(0), n_generations))
  @test p(extra_bits) == (BitVector(ca_bits), CANeuron{2,8}(DiscreteCA{2}(110), n_generations))
end

const CANeuronStack{S,N,W} = SVector{S,CANeuron{N,W}} where {S,N,W}

function Base.show(io::IO, ::CANeuronStack{Size,NStates,Width}) where {Size,NStates,Width}
  print(io, "CANeuronStack(size=$Size)")
end

function Base.show(io::IO, ::MIME"text/plain", cas::CANeuronStack{Size,NStates,Width}) where {Size,NStates,Width}
  print(io, "CANeuronStack(size=$Size) [")
  if !isempty(cas)
    first = true
    foreach(cas) do can
      if first
        print(io, "\n   ")
        first = false
      else
        print(io, "\n  ,")
      end

      show(io, can)
    end
    println(io)
  end
  println(io, "]")
end

function (cas::CANeuronStack{S,N,W})(state::State)::State where {S,N,W,State<:Row{N,W}}
  foldl(cas; init=state) do acc, can
    can(acc)
  end
end


@testitem "CANeuronStack" begin
  using StaticArrays
  function new_state(::Type{Val{L}}) where {L}
    let bla = zeros(Int, L)
      bla[1] = 1
      Row{2}(SizedVector{L}(bla))
    end
  end

  rule1 = 110
  rule2 = 30
  n_generations1 = 40
  n_generations2 = 20
  test_can1 = CANeuron{2,32}(DiscreteCA{2}(110), n_generations1)
  test_can2 = CANeuron{2,32}(DiscreteCA{2}(30), n_generations2)
  cas = CANeuronStack{2,2,32}(test_can1, test_can2)
  state = new_state(Val{32})
  @test cas(state) == test_can1(state) |> test_can2
end


function parser_bits_required(::Type{<:CANeuronStack{S,2}}; kw...) where {S}
  S * parser_bits_required(CANeuron{2}; kw...)
end

function parser(::Type{<:CANeuronStack{S,2,W}}; kw...) where {S,W}
  function p(bits::T)::Tuple{BitVector,CANeuronStack{S,2,W}} where {T<:AbstractArray}
    out = Vector{CANeuron{2,W}}(undef, S)
    can_parser = Musica.parser(CANeuron{2,W}; kw...)
    for idx in 1:S
      bits, can = can_parser(bits)
      out[idx] = can
    end
    (bits, CANeuronStack{S,2,W}(out))
  end
end

@testitem "CANeuronStack parsing" begin
  rule1 = 110
  rule2 = 30
  const bits_per_gen = 5
  n_generations1 = 5
  n_generations2 = 20
  gen_bits1 = digits(n_generations1; base=2, pad=bits_per_gen)
  gen_bits2 = digits(n_generations2; base=2, pad=bits_per_gen)
  ca1_bits = digits(rule1; base=2, pad=8)
  ca2_bits = digits(rule2; base=2, pad=8)
  full_bits1 = BitVector(vcat(gen_bits1, ca1_bits))
  full_bits2 = BitVector(vcat(gen_bits2, ca2_bits))

  test_can1 = CANeuron{2,32}(DiscreteCA{2}(110), n_generations1)
  test_can2 = CANeuron{2,32}(DiscreteCA{2}(30), n_generations2)

  p = Musica.parser(CANeuronStack{2,2,32}; bits_per_gen=Val{bits_per_gen})
  @test p(vcat(full_bits1, full_bits2)) == (Bool[], CANeuronStack{2}(test_can1, test_can2))
end