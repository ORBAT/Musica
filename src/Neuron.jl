using TestItems

abstract type Neuron{NStates,InWidth,OutWidth} end

struct CANeuron{NStates,Width,Fn} <: Neuron{NStates,Width,Width}
  _ca::CA.Elementary # HOX: abstrakti tyyppi koska UnionAll -->käpistely hidasta. Ei käytetä ku show:ssa tällä hetkellä
  _repeated_ca_fn::Fn
  _steps::Int

  function CANeuron{NStates,Width}(ca::CA.Elementary{NStates}, steps::Integer) where {NStates,Width}
    @assert steps > 0 "Number of steps must be >0"
    _g = Int(steps)
    fn = repeated(ca, _g)
    ## HOX: Core.Typeof saattaa ilm Teoriassa Joskus Ehkä olla hyvä idea funktio-valueiden (ja tyyppien) kanssa. Ks Bear
    new{NStates,Width,Core.Typeof(fn)}(ca, fn, _g)
  end
end

@inline function Base.hash(a::CANeuron{N,W}, h::UInt) where {N,W}
  hash(:CANeuron, h) |> @>(hash(N)) |> @>(hash(W)) |> @>(hash(a._ca)) |> @>(hash(a._steps))
end

@inline function Base.:(==)(a::CANeuron{N1,W1}, b::CANeuron{N2,W2}) where {N1,W1,N2,W2}
  isequal(N1, N2) && isequal(W1, W2) && isequal(a._steps, b._steps) && isequal(a._ca, b._ca)
end

## 

function Base.show(io::IO, can::CANeuron{NS,Width}) where {NS,Width}
  print(io, "CANeuron(", can._ca, ", width=", Width, ", steps=", can._steps, ")")
end

function Base.show(io::IO, ::MIME"text/plain", can::CANeuron{NS,Width}) where {NS,Width}
  print(io, can)
end

@inline function (can::CANeuron{N,W})(state::State)::State where {N,W,State<:Row{N,W}}
  can._repeated_ca_fn(state)
end

@inline bits_per_steps_default() = 5

const CANeuronStack{Size,NStates,StateWidth} =
  SVector{Size,CANeuron{NStates,StateWidth,Fn} where {Fn}}

function Base.show(io::IO, cas::CANeuronStack{Size,NStates,Width}) where {Size,NStates,Width}
  print(io, "CANeuronStack(Size=$Size,NStates=$NStates,Width=$Width)")
end

function Base.show(
  io::IO,
  ::MIME"text/plain",
  cas::CANeuronStack{Size,NStates,Width},
) where {Size,NStates,Width}
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