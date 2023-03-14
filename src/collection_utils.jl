using Transducers, TestItems, AutoHashEqualsCached, WhereTraits, StaticArrays, Static, MLStyle
using Transducers: start, inner, @next, wrap, unwrap, complete, Eduction
using MLStyle: @match

const SizedType{Len,T} = Union{StaticVector{Len,T}, NTuple{Len,T}}
export SizedType

"""
A `Some` that supports iteration and eg. `map`
```jldoctest
julia> Iterators.flatten(Optional{Int}[SSome(1), nothing, SSome(2)]) |> collect
2-element Vector{Any}:
 1
 2

julia> map(x -> 2x, SSome(1))
SSome(2)
```
"""
struct SSome{T}
  value::T
end

export SSome

struct None end
const none = None()

const Nothingness = Union{None,Nothing}

export None, none, Nothingness

const Optional{T} = Union{SSome{T},None}
export Optional

SSome(::Type{T}) where {T} = SSome{Type{T}}(T)

@inline Base.iterate(::None, @nospecialize(i...)) = nothing

@inline function Base.iterate(s::SSome{T}) where {T}
  (s.value, :done)
end

@inline Base.iterate(@nospecialize(_::SSome), @nospecialize(_::Symbol)) = nothing

@inline Base.IteratorSize(@nospecialize(_::Type{<:Optional})) = Base.HasLength()
@inline Base.length(@nospecialize(::SSome)) = 1
@inline Base.length(@nospecialize(::None)) = 0
@inline Base.IteratorEltype(@nospecialize(_::Type{None})) = Base.EltypeUnknown()
@inline Base.eltype(@nospecialize(_::Type{SSome{T}})) where {T} = T

@inline Base.promote_rule(::Type{SSome{T}}, ::Type{T}) where {T} = SSome{T}

@inline Base.convert(::Type{Optional{T}}, x) where {T} = SSome(convert(T, x))
@inline Base.convert(::Type{Optional{T}}, @nospecialize(::Nothing)) where {T} = none
@inline Base.convert(::Type{Optional{T}}, x::Optional{T}) where {T} = x

@inline Base.convert(::Type{T}, x::SSome{T}) where {T} = get_value(x)
@inline Base.convert(::Type{SSome}, x::T) where {T} = SSome{T}(x)
@inline Base.convert(::Type{SSome{T}}, x) where {T} = SSome{T}(convert(T, x))
@inline Base.convert(::Type{SSome{T}}, x::SSome) where {T} = SSome{T}(convert(T, x.value))

@inline Base.convert(::Type{Some{T}}, x::SSome) where {T} = Some{T}(convert(T, x.value))
@inline Base.convert(::Type{Some}, x::SSome{T}) where {T} = Some{T}(x.value)

@inline Base.convert(::Type{Nothing}, ::None) = nothing
@inline Base.convert(::Type{None}, ::Nothing) = none
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

function Base.show(io::IO, x::None)
  print(io, "none")
end

@inline Base.isnothing(::None) = true
@inline Base.notnothing(::None) = throw(ArgumentError("None passed to notnothing"))

@inline Base.something(::None, y...) = something(y...)
@inline Base.something(x::SSome, @nospecialize(y...)) = x.value

# HOX: Base.convert(::Type{Maybe{T}} […]) määritteleminen saa haillaan jopa kääntäjän nurin
#### ----> koska type piracy, ks esim https://github.com/JuliaLang/julia/issues/30805

# @inline Base.convert(::Type{Some{T}}, x::T) where {T} = Some(x)
# @inline Base.convert(::Type{T}, x::Some{T}) where {T} = get_value(x)
# @inline Base.:(==)(a::Some, b::Some) = isequal(get_value(a), get_value(b))
@inline Base.:(==)(a::SSome, b::SSome) = isequal(get_value(a), get_value(b))
@inline Base.:(==)(a, b::SSome) = isequal(promote(a, b)...)
@inline Base.:(==)(a::SSome, b) = isequal(promote(a, b)...)
@inline Base.:(==)(::None, ::Nothing) = true
@inline Base.:(==)(::Nothing, ::None) = true

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
  @test TakesOpt(nothing).a == none
  @test TakesOpt(none).a == none
end

## KYS: miks tyhjä tuple oli == nothing???
@inline issomething(x::T) where {T} = !isnothing(x) #= && x != () =#

function get_value end

@inline get_value() = throw(ArgumentError("No value arguments present"))
@inline get_value(x::Nothingness, y...) = get_value(y...)
## KYS: miks mulla oli tää tyhjä tuple ja NTuple{1} tässä?? Testit ainakin menee läpi ilman :D
# @inline get_value(x::Tuple{}, y...) = get_value(y...)
@inline get_value(x::Some, @nospecialize(y...)) = x.value
@inline get_value(x::SSome, @nospecialize(y...)) = x.value
# @inline get_value((x,)::NTuple{1}, @nospecialize(y...)) = x
@inline get_value(x::Any, @nospecialize(y...)) = x
# @inline get_value(x::Function, y...) = get_value(x(), y...)

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
  for nope = (:nothing, :none)
    @eval @test get_value($nope, 5) == 5
  end

  for yup = (:(Some(5)), :(SSome(5)), :5), nope = (:nothing, :none)
    @eval @test get_value($nope, $yup, $nope) == 5
  end
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
julia> map(x->2x, none)

```
"""
@inline Base.map(@nospecialize(f), ::None) = nothing

@inline maybe_collect(x) = x |> collect
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

const VectorLike{T,N} = Union{<:AbstractVector{T},<:NTuple{N,T}}

struct ZeroPadded{PadLen,E,T<:VectorLike{E}} <: AbstractVector{E}
  coll::T
  _coll_len::Int
  Base.@propagate_inbounds function ZeroPadded{PL,E,T}(coll) where {PL,E,T}
    let coll_len = length(coll)
      @boundscheck @assert coll_len ≤ PL "coll can't be longer than the pad length PL"
      new{PL,E,T}(coll, coll_len)
    end
  end
end

export ZeroPadded

@inline ZeroPadded{PadLen}(a) where {PadLen} = ZeroPadded{PadLen,Base.eltype(a),typeof(a)}(a)
## HOX: ei type stable koska n on dynaaminen!!!
# @inline ZeroPadded(a, n) = ZeroPadded{n,Base.eltype(a),typeof(a)}(a)

@inline _zp_pad_len(::Type{<:ZeroPadded{PadLen}}) where {PadLen} = PadLen
@inline _zp_pad_len(v::T) where {T<:ZeroPadded} = _zp_pad_len(T)

## FIXME
Base.show(io::IO, v::ZeroPadded{PL}) where {PL} = print(io, "ZeroPadded{", PL, "}[", join([x for x in v], ", "), "]")

Base.@propagate_inbounds function Base.getindex(v::ZeroPadded{PL,E}, idx::Int) where {PL,E}
  # @info "getindex idx" idx join(_stacktrace(5), "\n")
  @boundscheck checkbounds(v, idx)
  if idx > v._coll_len
    zero(E)
  else
    @inbounds v.coll[idx]
  end
end

@inline Base.size(@nospecialize(_::ZeroPadded{PL}), n) where {PL} = n == 1 ? PL : 1
@inline Base.size(@nospecialize(_::ZeroPadded{PL})) where {PL} = (PL,)
@inline Base.length(@nospecialize(_::ZeroPadded{PL})) where {PL} = PL
@inline Base.lastindex(@nospecialize(_::ZeroPadded{PL})) where {PL} = PL
@inline Base.axes(@nospecialize(_::ZeroPadded{PL})) where {PL} = (Base.OneTo(PL),)
@inline Base.firstindex(@nospecialize(_::ZeroPadded)) = 1
@inline Base.eltype(@nospecialize(_::ZeroPadded{PL,E})) where {PL,E} = E
@inline Base.IteratorEltype(@nospecialize(_::Type{<:ZeroPadded})) = Base.HasEltype()
@inline Base.IteratorEltype(@nospecialize(_::ZeroPadded)) = Base.HasEltype()
@inline Base.IteratorSize(@nospecialize(_::Type{<:ZeroPadded})) = Base.HasShape{1}()
@inline Base.parent(v::ZeroPadded) = v.coll

# @forward ZeroPadded.coll (Base.firstindex, Base.eltype, Base.IteratorEltype, Base.IteratorSize)

Base.@propagate_inbounds function Base.iterate(v::ZeroPadded{PL,E}, n=1) where {PL,E}
  if 0 < n > PL
    return nothing
  end

  item = if n > v._coll_len
    zero(E)
  else
    @inbounds v.coll[n]
  end
  (item, n + 1)
end

@testitem "ZeroPadded" begin
  let orig = [1, 2, 3]
    let zp = Musica.ZeroPadded{4}(orig)
      @test zp[1:3] == orig
      @test zp[4] == 0
      @test_throws BoundsError zp[5]
      @inline function fn()
        @inbounds zp[5]
      end
      @test fn() == 0
    end
  end
end


Base.@propagate_inbounds function droplast(arr::AbstractArray, n, max_len)
  # n = 1, max_len = 4
  # arr_len == max_len
  # arr = [1, 2, 3, 4]
  # --> tiputetaan vaan `n` kpl pois lopusta, return [1, 2]
  #
  # arr_len < max_len. diff = 1
  # arr = [1, 2, 3]
  # --> jos diff < n, tiputetaan `diff` kpl pois, return [1, 2]
  #
  # diff ≥ n. diff = 2
  # arr = [1, 2]
  # --> ei tehä mitään, return [1, 2]


  arr_len = length(arr)
  if arr_len == 0
    return arr
  end
  @boundscheck @assert arr_len ≤ max_len
  if arr_len != max_len
    len_diff = max_len - arr_len
    if len_diff < n
      n = len_diff
    else
      return @view arr[:]
    end
  end
  @inbounds @view arr[1:end-n]
end

Base.@propagate_inbounds function droplast(arr, n, max_len)
  # n = 1, max_len = 4
  # arr_len == max_len
  # arr = [1, 2, 3, 4]
  # --> tiputetaan vaan `n` kpl pois lopusta, return [1, 2]
  #
  # arr_len < max_len. diff = 1
  # arr = [1, 2, 3]
  # --> jos diff < n, tiputetaan `diff` kpl pois, return [1, 2]
  #
  # diff ≥ n. diff = 2
  # arr = [1, 2]
  # --> ei tehä mitään, return [1, 2]

  arr_len = length(arr)
  if arr_len == 0
    return arr
  end
  @boundscheck @assert arr_len ≤ max_len
  if arr_len != max_len
    len_diff = max_len - arr_len
    if len_diff < n
      n = len_diff
    else
      return arr[:]
    end
  end
  @inbounds arr[1:end-n]
end

@testitem "droplast" begin
  @test Musica.droplast([1, 2, 3], 2, 4) == [1, 2]
  @test Musica.droplast([], 2, 4) == []
end

export droplast

struct Toroidal{Radius,Len,E,T<:VectorLike{E}} <: AbstractVector{E}
  # coll::T
  # _coll_len::Int
  # Base.@propagate_inbounds function Toroidal{PL,E,T}(coll) where {PL,E,T}
  #   let coll_len = length(coll)
  #     @boundscheck @assert coll_len ≤ PL "coll can't be longer than the pad length PL"
  #     new{PL,E,T}(coll, coll_len)
  #   end
  # end
end

export Toroidal
#= 
@inline Toroidal{PadLen}(a) where {PadLen} = Toroidal{PadLen,Base.eltype(a),typeof(a)}(a)
# @inline Toroidal(a, n) = Toroidal{n,Base.eltype(a),typeof(a)}(a)

@inline _zp_pad_len(::Type{<:Toroidal{PadLen}}) where {PadLen} = PadLen
@inline _zp_pad_len(v::T) where {T<:Toroidal} = _zp_pad_len(T)

Base.show(io::IO, v::Toroidal{PL}) where {PL} = print(io, "Toroidal{", PL, "}[", join([x for x in v], ", "), "]")

Base.@propagate_inbounds function Base.getindex(v::Toroidal{PL,E}, idx::Int) where {PL,E}
  # @info "getindex idx" idx join(_stacktrace(5), "\n")
  @boundscheck checkbounds(v, idx)
  if idx > v._coll_len
    zero(E)
  else
    @inbounds v.coll[idx]
  end
end

@inline Base.size(@nospecialize(_::Toroidal{PL}), n) where {PL} = n == 1 ? PL : 1
@inline Base.size(@nospecialize(_::Toroidal{PL})) where {PL} = (PL,)
@inline Base.length(@nospecialize(_::Toroidal{PL})) where {PL} = PL
@inline Base.lastindex(@nospecialize(_::Toroidal{PL})) where {PL} = PL
@inline Base.axes(@nospecialize(_::Toroidal{PL})) where {PL} = (Base.OneTo(PL),)
@inline Base.firstindex(@nospecialize(_::Toroidal)) = 1
@inline Base.eltype(@nospecialize(_::Toroidal{PL,E})) where {PL,E} = E
@inline Base.IteratorEltype(@nospecialize(_::Type{<:Toroidal})) = Base.HasEltype()
@inline Base.IteratorEltype(@nospecialize(_::Toroidal)) = Base.HasEltype()
@inline Base.IteratorSize(@nospecialize(_::Type{<:Toroidal})) = Base.HasShape{1}()
@inline Base.parent(v::Toroidal) = v.coll

# @forward Toroidal.coll (Base.firstindex, Base.eltype, Base.IteratorEltype, Base.IteratorSize)

Base.@propagate_inbounds function Base.iterate(v::Toroidal{PL,E}, n=1) where {PL,E}
  if 0 < n > PL
    return nothing
  end

  item = if n > v._coll_len
    zero(E)
  else
    @inbounds v.coll[n]
  end
  (item, n + 1)
end

@testitem "Toroidal" begin
  let orig = [1,2,3]
    let zp = Musica.Toroidal{4}(orig)
      @test zp[1:3] == orig
      @test zp[4] == 0
      @test_throws BoundsError zp[5]
      @inline function fn()
        @inbounds zp[5]
      end
      @test fn() == 0
    end
  end
end =#
_to_toroidal_idx(i, radius, len) = mod(i - 2radius, len) + 1

"""
    similar_copy(coll)
Makes a `similar` copy of `coll`
"""
similar_copy(coll) = copyto!(coll |> similar, coll)
export similar_copy

@data List{T} begin
  Nil()
  Cons(head::T, tail::List{T})
end

Nil() = Nil{Any}()
Cons(head::T, tail::Nil{Any}) where {T}  = Cons(head, Nil{T}())

Base.length(@nospecialize(x::Nil)) = 0
Base.length(@nospecialize(xs::Cons)) = 1 + length(xs.tail)

(::Colon)(x::T, xs::List) where {T} = Cons(x, xs)

popfirst(xs::Cons) = xs.head
popfirst(@nospecialize(_::Nil)) = error("Cannot pop from empty List")
maybe_popfirst(xs::Cons) = SSome(xs.head)
maybe_popfirst(@nospecialize(_::Nil)) = none

head(xs::Cons) = xs.head
tail(xs::Cons) = xs.tail
head(@nospecialize(_::Nil)) = error("Cannot head from empty List")
tail(@nospecialize(_::Nil)) = error("Cannot tail from empty List")
maybe_head(xs::Cons) = SSome(xs.head)
maybe_tail(xs::Cons) = SSome(xs.tail)
maybe_head(@nospecialize(_::Nil)) = none
maybe_tail(@nospecialize(_::Nil)) = none
Base.first(xs::List) = head(xs)
Base.last(xs::Cons) = @match xs begin
  Cons(head, ::Nil) => head
  Cons(_, tail::Cons) => last(tail)
end
Base.last(@nospecialize(_::Nil)) = error("Cannot last from empty List")

Base.iterate(l::List, @nospecialize(_::Nil)) = nothing
Base.iterate(l::List, state::Cons = l) = (state.head, state.tail)