using Transducers, TestItems
using Transducers: start, inner, @next, wrap, unwrap, complete, Eduction

const Maybe{T} = Union{Some{T},Nothing}

@inline Base.convert(::Type{Some{T}}, x::T) where T = Some(x)
@inline Base.convert(::Type{T}, x::Some{T}) where T = get_value(x)
@inline Base.:(==)(a::Some{T}, b::Some{T}) where T = isequal(get_value(a), get_value(b))

@testitem "Some{T} conversions and equality" begin
  let a::Some{Int} = 10
    @test a isa Some{Int}
    @test a == Some(10)
  end

  let a::Int = Some(10)
    @test a isa Int
    @test a == 10
  end

  let a = Some(1), b = Some(1)
    @test a == b
  end
end

export Maybe, Something

@inline get_or_else(::Tuple{}, fallback::T) where {T} = fallback
@inline get_or_else(::Nothing, fallback::T) where {T} = fallback
@inline get_or_else(v::T, _fallback) where {T} = @inline get_value(v)

@inline issomething(x) = !isnothing(x) && x != ()

function get_value end

@inline get_value() = throw(ArgumentError("No value arguments present"))
@inline get_value(x::Nothing, y...) = get_value(y...)
@inline get_value(x::Tuple{}, y...) = get_value(y...)
@inline get_value(x::Some, y...) = x.value
@inline get_value((x,)::NTuple{1}, y...) = x
@inline get_value(x::Any, y...) = x

# map(f, x::Number, ys::Number...) = f(x, ys...)
# TODO: map(f, x::Maybe{T}, ys::Maybe{T}...) niin että kaikki x, ys... pitää olla Some

"""
```jldoctest
julia> map(x->2x, Some(1))
Some(2)
```
"""
@inline Base.map(f, x::Some) = Some(f(get_value(x)))

"""
```jldoctest
julia> map(x->2x, nothing)

```
"""
@inline Base.map(f, ::Nothing) = nothing

@testitem "Maybe" begin
  using Random
  struct Testes
    v::Maybe{Xoshiro}
  end

  @test Musica.get_or_else(Testes(Some(Xoshiro(666))).v, Xoshiro(1)) == Xoshiro(666)
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

function take(a, n)
  if length(a) ≤ n
    @inbounds @view a[:]
  else
    @inbounds @view a[1:n]
  end
end