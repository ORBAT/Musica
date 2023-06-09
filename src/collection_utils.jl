using Transducers, TestItems
using Transducers: start, inner, @next, wrap, unwrap, complete, Eduction
using AutoHashEqualsCached

abstract type Optional{T} end
export Optional

struct TNothing{T} <: Optional{T} end
export TNothing

function Base.show(io::IO, ::TNothing{T}) where {T}
  print(io, "tnothing(",T,")")
end

const Nothingness{T} = Union{Nothing,TNothing{T}}

"""
`Some` on steroids. See also [`tnothing`](@ref)
```jldoctest
julia> Iterators.flatten([SSome(1), tnothing(), SSome(2)]) |> collect
2-element Vector{Any}:
 1
 2

julia> map(x -> 2x, SSome(1))
SSome(2)
```
"""
struct SSome{T} <: Optional{T}
  value::T
end

export SSome

SSome(::Type{T}) where {T} = SSome{Type{T}}(T)

@inline Base.iterate(@nospecialize(::TNothing), @nospecialize(i...)) = nothing

@inline function Base.iterate(s::SSome{T})::Tuple{T, Int} where {T}
    (s.value, 2)
end

@inline function Base.iterate(s::SSome{T}, i)::Union{Nothing, Tuple{T, Int}} where {T}
  if i == 1
    (s.value, 2)
  end
end

Base.IteratorSize(@nospecialize(_::Type{<:Optional})) = Base.HasLength()
Base.length(@nospecialize(::SSome)) = 1
Base.length(@nospecialize(::TNothing)) = 0
Base.IteratorEltype(@nospecialize(_::Type{<:Optional})) = Base.HasEltype()
Base.eltype(::Type{<:Optional{T}}) where {T} = T

@inline Base.promote_rule(::Type{SSome{T}}, ::Type{SSome{S}}) where {T, S<:T} = SSome{T}

@inline Base.convert(::Type{T}, x::SSome{T}) where {T} = get_value(x)
@inline Base.convert(::Type{<:Optional{T}}, x::T) where {T} = SSome(x)
@inline Base.convert(::Type{<:Optional{T}}, ::Nothing) where {T} = tnothing(T)
@inline Base.convert(::Type{<:Optional{T}}, @nospecialize(::TNothing)) where {T} = tnothing(T)

# @inline Base.convert(::Type{SSome{T}}, x::T) where {T} = SSome(x)
@inline Base.convert(::Type{SSome{T}}, x::SSome) where {T} = SSome{T}(convert(T, x.value))::SSome{T}
@inline Base.convert(::Type{TNothing{T}}, @nospecialize(::TNothing)) where {T} = TNothing{T}()
# @inline Base.convert(::Type{Optional{T}}, @nospecialize(::TNothing)) where {T} = TNothing{T}()

function Base.show(io::IO, x::SSome)
  if get(io, :typeinfo, Any) == typeof(x)
      show(io, x.value)
  else
      print(io, "SSome(")
      show(io, x.value)
      print(io, ')')
  end
end


@inline Base.isnothing(@nospecialize(::TNothing)) = true
@inline Base.notnothing(@nospecialize(::TNothing)) = throw(ArgumentError("TNothing passed to notnothing"))

@inline Base.something(@nospecialize(::TNothing), y...) = something(y...)
@inline Base.something(x::SSome, @nospecialize(y...)) = x.value

tnothing(::Type{T}) where {T} = TNothing{T}()
tnothing(v) = tnothing(typeof(v))
tnothing() = tnothing(Any)

export TNothing, tnothing

# HOX: Base.convert(::Type{Maybe{T}} […]) määritteleminen saa parhaillaan jopa kääntäjän nurin
#### ----> koska type piracy, ks esim https://github.com/JuliaLang/julia/issues/30805

# @inline Base.convert(::Type{Some{T}}, x::T) where {T} = Some(x)
# @inline Base.convert(::Type{T}, x::Some{T}) where {T} = get_value(x)
# @inline Base.:(==)(a::Some, b::Some) = isequal(get_value(a), get_value(b))
@inline Base.:(==)(a::SSome, b::SSome) = isequal(get_value(a), get_value(b))
@inline Base.:(==)(a, b::SSome) = isequal(a, get_value(b))
@inline Base.:(==)(a::SSome, b) = isequal(get_value(a), b)

@testitem "conversions and equality" begin
  let a::SSome{Int} = 10
    @test a isa SSome{Int}
    @test a == SSome(10)
  end

  let a::Int = SSome(10)
    @test a isa Int
    @test a == 10
  end

  struct Bob
    a::Int
    b::String
  end

  Bob() = Bob(rand(Int), rand(100:200) |> @<(string(; base=16)))

  let bob1 = Bob(), bob2 = deepcopy(bob1)
    @test bob1 == bob2
    @test SSome(bob1) == SSome(bob2)
  end
  let a = SSome(1), b = SSome(1)
    @test a == b
  end

  struct TakesOpt
    a::Optional{Int}
  end

  @test TakesOpt(5).a == SSome(5)
  @test TakesOpt(nothing).a == tnothing(Int)
  @test TakesOpt(tnothing(Int)).a == tnothing(Int)
  @test TakesOpt(tnothing()).a == tnothing(Int)
end

@inline get_or_else(::Tuple{}, fallback)  = fallback
@inline get_or_else(::Nothing, fallback)  = fallback
@inline get_or_else(::TNothing{T}, fallback::T) where {T} = fallback
# HUOM: @nospecialize(_fallback) koska sitä arvoa ei koskaan käytetä, niin turha kääntää sen eri 
# tyypeille versioita
@inline get_or_else(v::T, @nospecialize(_fallback)) where {T} = @inline get_value(v)

@inline issomething(x::T) where {T} = !isnothing(x) && x != ()

function get_value end

@inline get_value() = throw(ArgumentError("No value arguments present"))
# @inline get_value(x::TNothing, y...) = get_value(y...)
@inline get_value(x::Nothingness, y...) = get_value(y...)
@inline get_value(x::Tuple{}, y...) = get_value(y...)
@inline get_value(x::Some, @nospecialize(y...)) = x.value
@inline get_value(x::SSome, @nospecialize(y...)) = x.value
@inline get_value((x,)::NTuple{1}, @nospecialize(y...)) = x
@inline get_value(x::Any, @nospecialize(y...)) = x
@inline get_value(x::Function, y...) = get_value(x(), y...)

export get_value

macro get_value(args...)
  expr = :(nothing)
  for arg in reverse(args)
      expr = :(val = $(esc(arg)); !isnothing(val) ? val : ($expr))
  end
  # something = GlobalRef(Base, :something)
  return :(something($expr))
end


@testitem "get_value" begin
  for nope = (:nothing, :(tnothing(Int)), :(()))
    @eval @test get_value($nope, 5) == 5
  end

  for yup = (:(Some(5)), :(SSome(5)), :(5,), :5), nope = (:nothing, :(tnothing(Int)), :(()))
    @eval @test get_value($yup, $nope) == 5
  end
  fn = x -> 2x
  @test get_value(() -> nothing, Some(fn)) == fn
end

# map(f, x::Number, ys::Number...) = f(x, ys...)
# TODO: map(f, x::Maybe{T}, ys::Maybe{T}...) niin että kaikki x, ys... pitää olla Some

"""
```jldoctest
julia> map(x->2x, SSome(1))
SSome(2)
```
"""
@inline Base.map(f, x::SSome) = SSome(f(get_value(x)))

"""
```jldoctest
julia> map(x->2x, nothing)

```
"""
@inline Base.map(f, @nospecialize(::Nothingness)) = nothing

# @testitem "Maybe" begin
#   using Random
#   struct Testes
#     v::Maybe{Xoshiro}
#   end

#   @test Musica.get_or_else(Testes(Some(Xoshiro(666))).v, Xoshiro(1)) == Xoshiro(666)
#   @test Musica.get_or_else(Testes(Xoshiro(666)).v, Xoshiro(1)) == Xoshiro(666)
#   @test Musica.get_or_else(Testes(nothing).v, Xoshiro(1)) == Xoshiro(1)
# end

export get_or_else

_Collectable = Union{Transducers.Foldable,AbstractRange}

@inline maybe_collect(x) = x
@inline maybe_collect(x::T) where {T<:_Collectable} = x |> collect
@inline maybe_collect(x::T) where {N,T<:NTuple{N,Any}} = map(maybe_collect, x)
@inline maybe_collect(x::T) where {T<:Optional} = map(maybe_collect, x)

export maybe_collect

"""
    LiftToArray()

A transducer that lifts its input into an array. Input must be finite.



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

Transducers.OutputSize(::Type{<:LiftToArray}) = Transducers.SizeChanging()
Transducers.isexpansive(::LiftToArray) = false

function take(a, n)
  if length(a) ≤ n
    @inbounds @view a[:]
  else
    @inbounds @view a[1:n]
  end
end