using TestItems, Test

abstract type Neuron{NStates,InWidth,OutWidth} <: Function end

struct CANeuron{NStates,Width} <: Neuron{NStates,Width,Width}
  ca::DiscreteCA
  repeated_ca_fn::Function
  generations::Int

  function CANeuron{NStates,Width}(ca::DiscreteCA{NStates}, gens::Integer) where {NStates,Width}
    @assert gens > 0 "Number of generations must be >0, was $gens"
    _g = Int(gens)
    new(ca, repeated(ca, _g), _g)
  end
end

@inline function Base.hash(a::CANeuron{N,W}, h::UInt) where {N,W}
  hash(:CANeuron, h) |> @©(hash(N)) |> @©(hash(W)) |> @©(hash(a.ca)) |> @©(hash(a.generations))
end

@inline function Base.:(==)(a::CANeuron{N1,W1}, b::CANeuron{N2,W2}) where {N1,W1,N2,W2}
  isequal(N1, N2) && isequal(W1, W2) && isequal(a.generations, b.generations) && isequal(a.ca, b.ca)
end

## 

function Base.show(io::IO, can::CANeuron{NS,Width}) where {NS,Width}
  print(io, "CANeuron($(can.ca), width=$Width, gens=$(can.generations))")
end

function Base.show(io::IO, ::MIME"text/plain", can::CANeuron{NS,Width}) where {NS,Width}
  print(io, "CANeuron($(can.ca), width=$Width, gens=$(can.generations))")
end


@inline function (can::CANeuron{N,W})(state::State)::State where {N,W,State<:Row{N,W}}
  can.repeated_ca_fn(state)
end

@inline bits_per_generation_default() = 5

parser_bits_required(::Type{<:CANeuron{2}}; bits_per_gen=bits_per_generation_default(), restkw...) = bits_per_gen + parser_bits_required(DiscreteCA{2}; restkw...)

@inline function parser(::Type{<:CANeuron{2,W}}; bits_per_gen=bits_per_generation_default()) where {W}
  Parser() do bits
    bitsleft, generations = parse_n_bits(bits, bits_per_gen)
    bitsleft, ca = parser(DiscreteCA{2})(bitsleft)
    #HUOM: generations+1 että saadaan aina vähintään 1 generation
    (bitsleft, CANeuron{2,W}(ca, Int(generations + 1)))
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
  const _bits_per_gen = 5
  #HUOM: -1 koska CANeuron lisää aina yhden. Ks CANeuron kommentit
  gen_bits = digits(n_generations - 1; base=2, pad=_bits_per_gen)
  ca_bits = digits(rule; base=2, pad=8)
  full_bits = BitVector(vcat(gen_bits, ca_bits))

  extra_bits = BitVector(vcat(gen_bits, ca_bits, ca_bits))

  p = Musica.parser(CANeuron{2,8}; bits_per_gen=_bits_per_gen)

  @test p(full_bits) == (Bool[], CANeuron{2,8}(DiscreteCA{2}(110), n_generations))
  @test p(BitVector(gen_bits)) == (Bool[], CANeuron{2,8}(DiscreteCA{2}(0), n_generations))
  @test p(extra_bits) == (BitVector(ca_bits), CANeuron{2,8}(DiscreteCA{2}(110), n_generations))
end

const CANeuronStack{Size,NStates,StateWidth} = SVector{Size,CANeuron{NStates,StateWidth}} where {Size,NStates,StateWidth}

function Base.show(io::IO, cas::CANeuronStack{Size,NStates,Width}) where {Size,NStates,Width}
  print(io, "CANeuronStack(Size=$Size,NStates=$NStates,Width=$Width)")
end

function Base.show(io::IO, ::MIME"text/plain", cas::CANeuronStack{Size,NStates,Width}) where {Size,NStates,Width}
  print(io, "CANeuronStack(Size=$Size,NStates=$NStates,Width=$Width) [")
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

@inline function (cas::CANeuronStack{S,N,W})(state::State)::State where {S,N,W,State<:Row{N,W}}
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

"""
Return the *maximum* number of bits required for a `CANeuronStack` when the maximum number of `CANeuron`s is `2^bits_per_stack_size`
"""
function parser_bits_required(::Type{<:CANeuronStack}; bits_per_stack_size::Int, kw...)
  bits_per_stack_size + 2^bits_per_stack_size * parser_bits_required(CANeuron{2}; kw...)
end

function parser(::Type{<:CANeuronStack{S,2,W}}; kw...) where {S,W}
  Parser() do bits
    out = Vector{CANeuron{2,W}}(undef, S)
    can_parser = Musica.parser(CANeuron{2,W}; kw...)
    for idx in 1:S
      bits, can = can_parser(bits)
      out[idx] = can
    end
    (bits, CANeuronStack{S,2,W}(out))
  end
end

function parser(::Type{<:CANeuronStack}; bits_per_stack_size=5, state_width=16, kw...)
  Parser() do bits
    bitsleft, _stack_size = bits |> @£(parse_n_bits(bits_per_stack_size))
    stack_size::Int = Int(_stack_size) + 1

    out = Vector{CANeuron{2,state_width}}(undef, Int(stack_size))
    can_parser = Musica.parser(CANeuron{2,state_width}; kw...)
    for idx in 1:stack_size
      bitsleft, can = can_parser(bitsleft)
      # @info out, idx, can
      # error("FUCK out=", out, " idx=", idx, " can=", can, "stack_size=", stack_size)
      out[idx] = can
    end
    (bitsleft, CANeuronStack{stack_size,2,state_width}(out))
  end
end

@testitem "CANeuronStack static size parsing" begin
  rule1 = 110
  rule2 = 30
  const _bits_per_gen = 5
  n_generations1 = 5
  n_generations2 = 20
  #HUOM: -1 koska CANeuron lisää aina yhden, ks CANeuron kommentit
  gen_bits1 = digits(n_generations1 - 1; base=2, pad=_bits_per_gen)
  gen_bits2 = digits(n_generations2 - 1; base=2, pad=_bits_per_gen)
  ca1_bits = digits(rule1; base=2, pad=8)
  ca2_bits = digits(rule2; base=2, pad=8)
  full_bits1 = BitVector(vcat(gen_bits1, ca1_bits))
  full_bits2 = BitVector(vcat(gen_bits2, ca2_bits))

  test_can1 = CANeuron{2,32}(DiscreteCA{2}(110), n_generations1)
  test_can2 = CANeuron{2,32}(DiscreteCA{2}(30), n_generations2)

  p = Musica.parser(CANeuronStack{2,2,32}; bits_per_gen=_bits_per_gen)
  @test p(vcat(full_bits1, full_bits2)) == (Bool[], CANeuronStack{2}(test_can1, test_can2))
end

@testitem "CANeuronStack dynamic size parsing" begin
  rule1 = 110
  rule2 = 30
  const _bits_per_gen = 5
  const _bits_per_stack_size = 2
  n_generations1 = 5
  n_generations2 = 20

  #HUOM: -1 koska CANeuron lisää aina yhden, ks CANeuron kommentit
  gen_bits1 = digits(n_generations1 - 1; base=2, pad=_bits_per_gen)
  gen_bits2 = digits(n_generations2 - 1; base=2, pad=_bits_per_gen)
  ca1_bits = digits(rule1; base=2, pad=8)
  ca2_bits = digits(rule2; base=2, pad=8)
  can1_bits = BitVector(vcat(gen_bits1, ca1_bits))
  can2_bits = BitVector(vcat(gen_bits2, ca2_bits))
  stack_size_bits = digits(1; base=2, pad=_bits_per_stack_size)
  full_bits = vcat(stack_size_bits, can1_bits, can2_bits)

  test_can1 = CANeuron{2,32}(DiscreteCA{2}(110), n_generations1)
  test_can2 = CANeuron{2,32}(DiscreteCA{2}(30), n_generations2)

  p = Musica.parser(CANeuronStack; bits_per_gen=_bits_per_gen, bits_per_stack_size=_bits_per_stack_size, state_width=32)

  @test Musica.parser_bits_required(CANeuronStack; bits_per_stack_size=2, bits_per_gen=2) == 4 * Musica.parser_bits_required(CANeuron{2}, bits_per_gen=2) + _bits_per_stack_size

  @test p(full_bits) == (Bool[], CANeuronStack{2}(test_can1, test_can2))
end

export CANeuron, CANeuronStack