using Transducers
using Transducers: start, inner, @next, wrap, unwrap, complete, Eduction

const Maybe{T} = Union{T,Nothing}

export Maybe

@inline get_or_else(::Nothing, fallback::T) where T = fallback
@inline get_or_else(v::T, _fallback) where T = v

@testitem "Maybe" begin
  using Random
  struct Testes
    v::Maybe{AbstractRNG}
  end

  @test Musica.get_or_else(Testes(Xoshiro(666)).v, Xoshiro(1)) == Xoshiro(666)
  @test Musica.get_or_else(Testes(nothing).v, Xoshiro(1)) == Xoshiro(1)
end

export get_or_else

_Collectable = Union{Transducers.Foldable, AbstractRange}

@inline maybe_collect(x) = x
@inline maybe_collect(x::T) where {T<:_Collectable} = x |> collect
@inline maybe_collect(x::T) where {N, T<:NTuple{N, Any}} = map(maybe_collect, x)

export maybe_collect

"""
    LiftToArray()

A transducer that lifts its input into an array.

```jldoctest; setup=:(using Transducers)
# using Transducers
julia> [1,0,1] |> Map(x -> 2x) |> LiftToArray() |> Map(x -> undigits(x,3)) |> collect
1-element Vector{UInt64}:
 0x0000000000000014
```
"""
struct LiftToArray <: Transducer end

export LiftToArray

const _LiftRType = Transducers.R_{LiftToArray}

@inline Transducers.start(rf::_LiftRType, result) =
  Transducers.wrap(rf, Union{}[], Transducers.start(Transducers.inner(rf), result))

@inline function Transducers.next(rf::_LiftRType, result, input)
  Transducers.wrapping(rf, result) do buffer, iresult
    push!!(buffer, input), iresult
  end
end

@inline function Transducers.complete(rf::_LiftRType, result)
  buffer, iresult = Transducers.unwrap(rf, result)
  iresult = Transducers.@next(Transducers.inner(rf), iresult, buffer)
  Transducers.complete(Transducers.inner(rf), iresult)
end