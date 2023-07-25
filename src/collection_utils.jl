using Transducers,
  TestItems, AutoHashEquals, StaticArrays, Static, MLStyle, Try, TryExperimental,
  Accessors
using Transducers: Eduction
using MLStyle: @match
using TypeUtils

using Base: tail
using StaticArrays: push, pop

const SizedType{Len,T} = Union{StaticVector{Len,T},NTuple{Len,T}}
export SizedType

using MacroTools: @> as @>>, @>> as @<<

@inline left((a,)::NTuple{1}) = a
@inline left(a, _...) = a
@inline left((a, _)) = a
@inline right(_, b) = b
@inline right((_, b)) = b

export left, right

#! format: off
"""
A `Some`-like type that supports iteration which means operations like `map` and `filter` work, and integrates with `Try` so that `Try.or_else`, `@?`, `Try.map` (in addition to `Base.map`) etc work.

Its counterpart is `none` / `None()`, but in most cases `nothing` can be substituted for `none` as they're both convertible to and equal each other.

```jldoctest
# note that the vector has to be an Optional{Int}[] for this to work.
julia> Iterators.flatten(Optional{Int}[Just(1), nothing, Just(2)]) |> collect
2-element Vector{Any}:
 1
 2

julia> let frob_value = Just(1);  map(x -> 2x, Just(1)) end
Just(2)

julia> map(x -> 2x, none)

```
"""
struct Just{T}
  value::T
end
#! format: on
Just(::Type{T}) where {T} = Just{Type{T}}(T)
export Just

struct None end
const none = None()
const Nothingness = Union{None,Nothing}
export None, none, Nothingness

const Optional{T} = Union{Just{T},None}
Optional(x) = Just(x)
Optional{T}(x) where {T} = Just{T}(x)
Optional{T}(::Nothingness) where {T} = none
Optional(::Nothingness) = none
export Optional

# _lift(To::Type, x, ::False) =
#   Try.Err(ArgumentError(LazyString("don't know how to lift value ", x, " to type ", To)))
# _lift(::Type{To}, x, ::True) where {To} = @trying convert(To, x)
# lift(To::Type{<:Optional}, x) = _lift(To, x, maybe_convertible(To, typeof(x)))

Base.hash(x::Just, h::UInt) = hash(x.value, hash(:Just, h))
Base.hash(::None, h::UInt) = hash(:none, h)

@inline Base.isnothing(::None)  = true
@inline Base.notnothing(::None) = throw(ArgumentError("none passed to notnothing"))

@inline Base.something(::None, y...) = some(y...)
@inline Base.something(x::Just, @nospecialize(y...)) = x.value

@testitem "Base.something" begin
  @test something(none, 5) == 5
  @test something(none, Just(5)) == 5
end

"""
    some(a, b, c)

convenience shortcut for [`Base.something`](@ref)
"""
const some::typeof(Base.something) = Base.something
export some

function _somemacro(args...)
  expr = :(nothing)
  for arg in reverse(args)
    expr = :(val = $(esc(arg)); val != $nothing ? val : $expr)
  end

  return :($something($expr))
end

"""
    @some a none 123

Same as [`Base.@something`](@ref) but supports [`none`](@ref)
"""
macro some(args...)
  return _somemacro(args...)
end

#! format: off
"""
    @ifsomething(body, this, orelse)

    ```jldoctest; output = false
        6 == @ifsomething(Just(1)) do x
          x + 5
        end

    # output
    true
    ```

    666 == @ifsomething(none, 666) do x
      x + 5
    end

    10 == @ifsomething(x->2x, Just(5))

A macro that runs the expression in `body` if `issomething(this)` is true. If `body` is an anonymous function `a -> dosomething_to(a)` or a `do` block, the "unwrapped" value of `this` will be passed to it in the one parameter it defines. `body` is run as an inline expression even if it's defined like an anonymous function / `do`-block. Short-circuiting: `body` isn't evaluated if `!issomething(this)`

The macro returns whatever `body` returns, meaning that the result value isn't "lifted" into a `Just`.
"""
macro ifsomething(body, this, orelse=nothing)
  return _ifsomething(body, this, orelse, __source__)
end
#! format: on

# if body is an anonymous function like qux -> fn(qux), returns the name of the function parameter (qux). If 
function _paramname_from_body(body, this)
  # the body is an anonymous function of some sort, either an arrow function or a do-block
  arg = if isexpr(body, :(->))
    exprargs = body.args[1]
    if exprargs isa Symbol # body is `x -> blah`
      esc(exprargs)
    else
      # body is `(tupleargs...) -> blah`, so `exprargs` is a `Expr(:tuple, tupleargs...)`, where `tupleargs` might be empty
      tupleargs = exprargs.args
      esc(only(tupleargs))
    end
  end
  isnothing(arg) ? gensym("ifsomething") : arg
end

function _get_body_expression(body, this)
  _argname = _paramname_from_body(body, this)
  if isexpr(body, :(->))
    # body is param -> body_expression,  Expr(:(->), param, body_expression)
    return _argname, esc(body.args[2])
  else
    # NOTE: defaults to calling the body with `$_argname`, but this might blow up in some cases?
    return _argname, :($(esc(body))($_argname))
  end
end

function _ifsomething(body, this, orelse, line)
  argname, bodyex = _get_body_expression(body, this)
  issomething = GlobalRef(Musica, :issomething)
  return quote
           let mayberesult = $(esc(this))
             if $issomething(mayberesult)
               let $argname = $something(mayberesult)
                 $bodyex
               end
             else
               $(esc(orelse))
             end
           end
         end |> MacroTools.flatten |> replace_linenums!(line)
end

@testitem "@ifsomething" begin
  @test @ifsomething(Just(1)) do x
    x + 5
  end == 6

  @test @ifsomething(none, 666) do x
    x + 5
  end == 666

  a = 666
  @test @ifsomething(none, a) do x
    x + 5
  end == 666

  @test @ifsomething(Just(1)) do x
    x + 5
  end isa Integer

  let justfn = x -> Just(x)
    @test @ifsomething(justfn(55)) do x
      x + 5
    end == 60
  end

  @test @ifsomething(typeof, Just(5)) == typeof(5)
end

export @some, @ifsomething

@inline Base.:(==)(a::Just, b::Just)                  = isequal(some(a), some(b))
@inline Base.:(==)(::Nothing, @nospecialize(_::Just)) = false
@inline Base.:(==)(@nospecialize(_::Just), ::Nothing) = false
@inline Base.:(==)(::None, ::Nothing)                 = true
@inline Base.:(==)(::Nothing, ::None)                 = true

# """
#     not_convertible(::Type{<:Just}, ::Type{<:Nothingness}) = static(true)

# A `None` or `Nothing` can't be converted to a `Just` even though `Base.convert(::Type{<:Just}, x::Nothingness)` is defined
# """
# not_convertible(::Type{<:Just}, ::Type{<:Nothingness}) = static(true)

@inline Base.convert(::Type{<:Just}, x::Nothingness) =
  throw(InexactError(:convert, Just, x))
@inline Base.convert(::Type{Just{T}} where {T}, x::Nothingness) =
  throw(InexactError(:convert, Just, x))

@inline Base.convert(::Type{<:Optional}, ::Nothingness)              = none
@inline Base.convert(::Type{<:Optional{T}} where {T}, ::Nothingness) = none
@inline Base.convert(::Type{None}, ::Nothing)                        = none

# HUOM: toimii sekä convert(Optional, 1) että convert(Optional{Int},1)
@inline Base.convert(::Type{<:Optional{T}}, x) where {T}          = Just(@isdefined(T) ? convert(T, x) : x)
@inline Base.convert(::Type{<:Optional{T}}, x::Just) where {T}    = begin
  T′ = @useifdefined(T, eltype(x))
  Just{T′}(as(T′, some(x)))
end
@inline Base.convert(::Type{<:Optional{T}}, x::Just{T}) where {T} = x
@inline Base.convert(::Type{<:Optional}, x::S) where {S}          = Just{S}(x)
@inline Base.convert(::Type{<:Optional}, x::Just)                 = x

@inline Base.convert(::Type{Just{T}}, x::Just{T}) where {T}      = x
@inline Base.convert(::Type{Just{T}}, x::Just{S}) where {T,S<:T} = Just{T}(some(x))
@inline Base.convert(::Type{Just{T}}, x::Just) where {T}         = Just{T}(convert(T, some(x)))

@inline Base.convert(::Type{Some}, x::Just{T}) where {T}         = Some{T}(something(x))
@inline Base.convert(::Type{Some{T}}, x::Just) where {T}         = Some{T}(convert(T, something(x)))
@inline Base.convert(::Type{Some{T}}, x::Just{S}) where {T,S<:T} = Some{T}(something(x))

"""
    bleb(x::OptOrValue{T}) = 

Shortcut type to eg. signal that a function parameter accepts either a straight-up `T` or an `Optional{T}`.
"""
const OptOrValue{T} = Union{Optional{T},T,Nothing}
export OptOrValue

@inline Base.iterate(s::Just)                                       = (s.value, nothing)
@inline Base.iterate(::None, @nospecialize(i...))                   = nothing
@inline Base.iterate(@nospecialize(_::Just), @nospecialize(_::Any)) = nothing

@inline Base.length(@nospecialize(::Just)) = 1
@inline Base.length(::None) = 0
@inline Base.eltype(::Type{Just{T}}) where {T} = T
@inline Base.IteratorEltype(::Type{None}) = Base.EltypeUnknown()

# NOTE: these make eg. Try.@and, Try.@or, Try.and_then etc work for Just & None
TryExperimental.branch(some::Just) = TryExperimental.Continue(some)
TryExperimental.branch(::None) = TryExperimental.Break(none)
TryExperimental.valueof(br::TryExperimental.Continue{<:Just}) = some(br.result)
TryExperimental.valueof(::TryExperimental.Break{None}) = nothing

# These make Try.map work for Just & None
Try.unwrap(result::Just) = result.value
Try.unwrap(result::None) = throw(ArgumentError("Try.unwrap called on a None"))

Try.isok(@nospecialize(_::Just)) = true
Try.isok(_::None)                = false

Try.iserr(@nospecialize(_::Just)) = false
Try.iserr(_::None)                = true

Try.unwrap_err(@nospecialize(_::Just)) = throw(ArgumentError("Try.unwrap_err called on a Just"))
Try.unwrap_err(::None)                 = nothing

# NOTE: a copy of Base.show for Some
Base.show(io::IO, x::Just{T}) where {T} =
  if get(io, :typeinfo, Any) == typeof(x)
    show(io, some(x))
  else
    print(io, "Just(")
    show(io, some(x))
    print(io, ')')
  end

Base.show(io::IO, x::None) = print(io, "none")

StaticArrays.push(::None, x) = Just(x)
StaticArrays.pop(xs::Just) = some(xs)
StaticArrays.pop(::None) = error("Cannot pop from None")
StaticArrays.push(@nospecialize(_::Just)) = error("Cannot push in to Just")

# HOX: Base.convert(::Type{Maybe{T}} […]) määritteleminen saa haillaan jopa kääntäjän nurin
#### ----> koska type piracy, ks esim https://github.com/JuliaLang/julia/issues/30805

@testitem "Just" begin
  let a::Just{Int} = 10
    @test a isa Just{Int}
    @test a == Just(10)
  end

  @test Just(1) == Just(1)
  @test Just(1) == Just(1.0)
  @test (Just(1) != nothing)
  @test (nothing != Just(1))
  @test nothing == none
  @test none == nothing

  @test convert(Optional, nothing) === none
  @test convert(Optional, none) === none
  @test convert(Optional{Int}, none) === none
  @test convert(Optional{Int}, nothing) === none

  @test convert(Optional, Just(1)) === Just(1)
  @test convert(Optional{Bool}, Just(1)) === Just(true)
  @test convert(Optional{Int}, Just(1)) === Just(1)
  @test convert(Just{Bool}, Just(1)) === Just(true)
  @test convert(Just{Int}, Just(1)) === Just(1)

  @test_throws InexactError convert(Just, nothing)
  @test_throws InexactError convert(Just, none)
  @test_throws InexactError convert(Just{Int}, none)
  @test_throws InexactError convert(Just{Int}, nothing)

  @test convert(Just{Number}, Just(1)) isa Just{Number}
  @test convert(Just, 5) == Just(5)

  struct Bob
    a::Int
    b::String
  end
  Bob() = Bob(rand(Int), rand(100:200) |> @<(string(; base=16)))

  let bob1 = Bob(), bob2 = deepcopy(bob1)
    @test bob1 == bob2
    @test Just(bob1) == Just(bob2)
  end

  struct TakesOpt
    a::Optional{Int}
  end

  @test TakesOpt(5).a === Just(5)
  @test TakesOpt(Just(5)).a === Just(5)
  @test TakesOpt(nothing).a === none
  @test TakesOpt(none).a === none

  let a::Optional{Integer}, b::Optional{Int} = Just(1)
    a = b
    @test a == b
  end
end

@testitem "Try integration" begin
  using Try, TryExperimental
  let fn() = @? Just(1)
    @test fn() === 1
  end

  let fn() = (@? none; 5)
    @test fn() == nothing
  end

  let bob = Try.or_else(x -> 2x, Just(5))
    @test bob === Just(5)
  end

  let bob = Try.or_else(_ -> 666, none)
    @test bob === 666
  end

  let bob = Try.and_then(x -> 2x, Just(5))
    @test bob === 10
  end

  let bob = Try.and_then(_ -> 666, none)
    @test bob === none
  end
end

@inline issomething(x::T) where {T} = !isnothing(x) #= && x != () =#
export issomething

# map(f, x::Number, ys::Number...) = f(x, ys...)
# TODO: map(f, x::Maybe{T}, ys::Maybe{T}...) niin että kaikki x, ys... pitää olla Some

"""
```jldoctest
julia> map(x -> 2x, Just(1))
Just(2)
```
"""
@inline Base.map(f, x::Just) = Just(f(some(x)))

"""
```jldoctest
julia> map(x -> 2x, none)

```
"""
@inline Base.map(@nospecialize(f), ::None) = nothing

"""
    LiftToArray()

A transducer that lifts its input into an array. Input must be finite.

```jldoctest; setup=:(using Transducers)
julia> [1, 0, 1] |> Map(x -> 2x) |> LiftToArray() |> Map(x -> undigits(x, 3)) |> collect
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
    return push!!(buffer, input), iresult
  end
end

@inline function Transducers.complete(rf::_LiftRType, result)
  buffer, iresult = Transducers.unwrap(rf, result)
  iresult = Transducers.@next(Transducers.inner(rf), iresult, buffer)
  return Transducers.complete(Transducers.inner(rf), iresult)
end

Transducers.OutputSize(::Type{<:LiftToArray}) = Transducers.SizeChanging()
Transducers.isexpansive(::LiftToArray) = false

vtake(a, n) =
  if length(a) ≤ n
    @inbounds @view a[:]
  else
    @inbounds @view a[1:n]
  end

const VectorLike{T,N} = Union{<:AbstractVector{T},<:NTuple{N,T}}

struct ZeroPadded{PadLen,E,T<:VectorLike,PW} <: AbstractVector{E}
  coll::T
  _coll_len::Int
  _pad_len::Int
  _pad_with::PW
  Base.@propagate_inbounds function ZeroPadded{PL}(coll; padwith=coll |> eltype |> zero) where {PL}
    let coll_len = length(coll), PWT = typeof(padwith), T = typeof(coll), E = eltype(coll)
      @boundscheck @assert coll_len ≤ PL "coll can't be longer than the pad length PL"
      new{Tuple{StaticInt(PL)},promote_type(E, PWT),T,PWT}(
        coll,
        coll_len,
        PL,
        padwith,
      )
    end
  end

  Base.@propagate_inbounds function ZeroPadded(coll, pad_len::Int; padwith=coll |> eltype |> zero)
    let coll_len = length(coll), PWT = padwith |> typeof, T = typeof(coll), E = eltype(coll)
      new{StaticArrays.Dynamic(),promote_type(E, PWT),T,PWT}(
        coll,
        coll_len,
        pad_len,
        padwith,
      )
    end
  end
end

@inline ZeroPadded(a, ::StaticInt{pad_len}; padwith=a |> eltype |> zero) where {pad_len} =
  ZeroPadded{pad_len}(a; padwith)

@inline _zp_padlen(z::ZeroPadded) = z._pad_len
Base.@assume_effects :foldable @inline _zp_padlen(::ZeroPadded{PadLen}) where {PadLen<:Tuple} =
  PadLen.parameters[1] |> known

Base.show(io::IO, v::ZeroPadded{PL}) where {PL} =
  print(io, "ZeroPadded{", PL, "}[", join([x for x in v], ", "), "]")

Base.@propagate_inbounds function Base.getindex(v::ZeroPadded{PL,E}, idx::Int) where {PL,E}
  @boundscheck checkbounds(v, idx)

  if idx <= v._coll_len
    v.coll[idx]
  else
    v._pad_with
  end
end

@inline Base.size(@nospecialize(z::ZeroPadded), n) = (n == 1 ? z |> _zp_padlen : 1)
@inline Base.size(@nospecialize(z::ZeroPadded)) = (z |> _zp_padlen,)
@inline Base.length(@nospecialize(z::ZeroPadded)) = z |> _zp_padlen
@inline Base.lastindex(@nospecialize(z::ZeroPadded)) = z |> _zp_padlen
@inline Base.axes(@nospecialize(z::ZeroPadded)) = (Base.OneTo(z |> _zp_padlen),)

Base.@assume_effects :foldable @inline Base.size(_::ZeroPadded{PL}, n) where {PL<:Tuple} =
  (n == 1 ? PL.parameters[1] : 1) |> known
Base.@assume_effects :foldable @inline Base.size(_::ZeroPadded{PL}) where {PL<:Tuple} =
  (PL.parameters[1] |> known,)
Base.@assume_effects :foldable @inline Base.length(_::ZeroPadded{PL}) where {PL<:Tuple} =
  PL.parameters[1] |> known
Base.@assume_effects :foldable @inline Base.lastindex(_::ZeroPadded{PL}) where {PL<:Tuple} =
  PL.parameters[1] |> known
Base.@assume_effects :foldable @inline Base.axes(_::ZeroPadded{PL}) where {PL<:Tuple} =
  (Base.oneto(PL.parameters[1]),)

# FIXME: not generic in the slightest
Base.@assume_effects :foldable @inline Base.firstindex(@nospecialize(_::ZeroPadded)) = 1
Base.@assume_effects :foldable @inline Base.eltype(_::ZeroPadded{PL,E}) where {PL,E} = E
Base.@assume_effects :foldable @inline Base.IteratorEltype(@nospecialize(_::Type{<:ZeroPadded})) =
  Base.HasEltype()
Base.@assume_effects :foldable @inline Base.IteratorEltype(@nospecialize(_::ZeroPadded)) =
  Base.HasEltype()
Base.@assume_effects :foldable @inline Base.IteratorSize(@nospecialize(_::Type{<:ZeroPadded})) =
  Base.HasShape{1}()
@inline Base.parent(v::ZeroPadded) = v.coll

Base.@propagate_inbounds function Base.iterate(v::ZeroPadded{PL,E}, n=1) where {PL,E}
  if 0 < n > _zp_padlen(v)
    return nothing
  end

  item = if n > v._coll_len
    zero(E)
  else
    @inbounds v.coll[n]
  end
  return (item, n + 1)
end

export ZeroPadded

@testitem "ZeroPadded" begin
  const _pad_to = 4
  let orig = [1, 2, 3]
    for zp in (Musica.ZeroPadded(orig, _pad_to), Musica.ZeroPadded{_pad_to}(orig))
      @eval begin
        let zp = $zp, orig = $orig
          @test zp[1:3] == orig
          @test zp[4] == 0
          @test zp |> length == _pad_to
          @test_throws BoundsError zp[5]
          @inline fn() = @inbounds zp[5]
          # FIXME: toimii jos testit ajaa VSCodella, mutta ei jos ne ajaa REPListä????
          @test fn() == 0
        end
      end
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
    # HOX: ei arr[:] koska muuten tää olis type unstable, koska paluuarvo olis 
    # Union{
    #  SubArray{Int64, 1, Vector{Int64}, Tuple{Base.Slice{Base.OneTo{Int64}}}, true},
    #  SubArray{Int64, 1, Vector{Int64}, Tuple{UnitRange{Int64}}, true}}
    return @view arr[1:end]
  end
  @boundscheck @assert arr_len ≤ max_len
  if arr_len != max_len
    len_diff = max_len - arr_len
    if len_diff < n
      n = len_diff
    else
      return @view arr[1:end]
    end
  end
  @inbounds @view arr[1:end-n]
end

@inline droplast(arr::AbstractArray, n) = @inbounds begin
  @view arr[1:end-n]
end

Base.@constprop :aggressive @inline droplast(arr::SizedVector{0}, _) = SizedVector{0}(@view arr[:])

# HOX: n on paree olla StaticInt
Base.@constprop :aggressive @inline function droplast(
  arr::StaticVector{L},
  n,
) where {L}
  arr_parent = arr |> parent
  # NOTE: @inbounds is safe here because if n≥L, the slice would just give an empty array/view
  @inbounds begin
    SizedVector{max(0, L - n)}(@view arr_parent[1:end-n])
  end
end

@propagate_inbounds droplast(arr, n) = arr[1:end-n]

"""
HOX: `n` täytyy olla `static(jotain)` tai esim. tyyppiparametrista tmv staattisesta lähteestä ettei tää oo type unstable, koska `n` vaikuttaa paluuarvon tyyppiin
"""
Base.@constprop :aggressive Base.@propagate_inbounds function droplast(
  arr::NTuple{N,T},
  n,
) where {N,T}
  n ≥ N && return ()
  return NTuple{max(0, N - n)}(arr[1:end-n])
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
      return arr
    end
  end
  @inbounds arr[1:end-n]
end

@testitem "droplast" begin
  @test Musica.droplast([1, 2, 3], 2, 4) == [1, 2]
  @test Musica.droplast([], 2, 4) == []
end

export droplast

# struct Toroidal{Radius,Len,E,T<:VectorLike{E}} <: AbstractVector{E}
# coll::T
# _coll_len::Int
# Base.@propagate_inbounds function Toroidal{PL,E,T}(coll) where {PL,E,T}
#   let coll_len = length(coll)
#     @boundscheck @assert coll_len ≤ PL "coll can't be longer than the pad length PL"
#     new{PL,E,T}(coll, coll_len)
#   end
# end
# end

# export Toroidal
#= 
@inline Toroidal{PadLen}(a) where {PadLen} = Toroidal{PadLen,Base.eltype(a),typeof(a)}(a)
# @inline Toroidal(a, n) = Toroidal{n,Base.eltype(a),typeof(a)}(a)

@inline _zp_padlen(::Type{<:Toroidal{PadLen}}) where {PadLen} = PadLen
@inline _zp_padlen(v::T) where {T<:Toroidal} = _zp_padlen(T)

Base.show(io::IO, v::Toroidal{PL}) where {PL} = print(io, "Toroidal{", PL, "}[", join([x for x in v], ", "), "]")

Base.@propagate_inbounds function Base.getindex(v::Toroidal{PL,E}, idx::Int) where {PL,E}
  # @debug "getindex idx" idx join(_stacktrace(5), "\n")
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

"""
    _to_toroidal_idx(idx, radius, len)

convert `idx` to a "toroidal" index, making it seem like a length `len` collection's first `radius` elements are the same as its last `radius` elements, and vice versa.
"""
_to_toroidal_idx(idx, radius, len) = mod(idx - 2radius, len) + 1

"""
    similar_copy(coll)

Makes a `similar` copy of `coll`
"""
similar_copy(coll) = copyto!(coll |> similar, coll)
export similar_copy

const Undef = UndefInitializer

"""
    List{T}

An immutable "cons list". See [`list`](@ref) and [`(::Colon)(x, xs::List)`](@ref) for building lists.

### FIXME[low-prio] (if possible): supports heterogenous types but it's currently really inefficient; prepending an element of a different type than the tail currently requires rebuilding the entire tail
"""
abstract type AbstractList{T} end

"""
    Nil{T} <: AbstractList{T}

Nil element of a [`List`](@ref). See [`Nil()`](@ref)
"""
struct Nil{T} <: AbstractList{T} end

"""
    Nil()
    Musica.nil

`Nil()` called without any type parameters starts an empty "typeless" list, which can be converted into a `List` of any type. `Nil{Any}()` starts an empty list that's explicitly of type `List{Any}`.

`nil` is provided as a shortcut for `Nil()`. It's not exported so it won't pollute the namespace, as it's a very short identifier.

```jldoctest
julia> using Musica: nil;

julia> lst = nil;

julia> push(lst, 1)
List{Int64}(1)

julia> lst2 = Nil{Any}();

julia> push(lst2, 1)
List{Any}(1)
```
"""
Nil() = Nil{Undef}()
const nil = Nil()

Base.isempty(@nospecialize(_::Nil)) = true

"""
    Cons(x, xs)

Used for building `List`s. See [`list`](@ref) and [`(::Colon)(x, xs::List)`](@ref) for shortcuts.

### KYSYM: pitäisköhän tän olla mutable struct (ja fieldit sit `const`eja), apinoiden DataStructures.jl:ää (https://github.com/JuliaCollections/DataStructures.jl/blob/c4b8b5faf5b02935eea1744a548dd9e308bfc230/src/list.jl)? Sillon se päätyis todennäkösemmin heappiin ja call-by -semantiikka olis enemmän pointterihko, mutta tiedä sit olisko tästä hyötyä vai enemmänkin haittaa kun tulis enemmän indirektiota
"""
struct Cons{T} <: AbstractList{T}
  head::T
  tail::Union{Nil{T},Cons{T}}
end

Base.isempty(@nospecialize(_::Cons)) = false

const List{T} = Union{Nil{T},Cons{T}}

Cons(x::T, xs::Cons{T}) where {T} = Cons{T}(x, xs)

Cons(x, _::Nil{Any}) = Cons{Any}(x, nil)
Cons(x, ::Nil{Undef}) = Cons{typeof(x)}(x, nil)

# constructs a heterogenous list.
# FIXME[low-prio]: more efficient heterogenous list construction, now this has to convert the tail to the common type
function Cons(x::T, xs::Cons{S}) where {T,S}
  T′ = _heterog_cons_eltype(T, S)
  return Cons{T′}(x, as(AbstractList{T′}, xs))
end

_heterog_cons_eltype(T::Type, S::Type) =
# TODO: should we use promote_type to see if we could use something other than a union? Or is using a union less surprising since there won't be any conversions? eg. promote_type(Int,Float64) --> Float64, so this doesn't seem too great. Maybe promote_typejoin?
  let U = Union{T,S}
    if !Core.Compiler.issimpleenoughtype(U)
      Any
    else
      U
    end
  end

Base.convert(::Type{AbstractList{T}}, xs::Cons{T}) where {T} = xs

# FIXME[low-prio]: more efficient heterogenous list construction, now this has to convert the tail to the common type
function Base.convert(::Type{AbstractList{T}}, xs::Cons{S}) where {S,T}
  return Cons{T}(as(T, xs.head), as(AbstractList{T}, xs.tail))
end
Base.convert(::Type{Union{Nil{T},Cons{T}}}, xs::Nil{T}) where {T} = xs
Base.convert(::Type{Union{Nil{T},Cons{T}}}, ::Nil{Undef}) where {T} = Nil{T}()
Base.convert(::Type{Nil{T}}, ::Nil{Undef}) where {T} = Nil{T}()
Base.convert(::Type{AbstractList{T}}, @nospecialize(_::Nil)) where {T} = Nil{T}()

# FIXME: recursive
_list(acc, v) = v:acc
_list(acc, v, rest...) = _list(v:acc, rest...)

"""
    list(1,2,3,4)

Creates a `List` with the given elements, which must be of the same type (use `List{T}(vs...)` to explicitly specify the type of the list)

ATTN: recursive so it's not a good idea to call it with a long `v`. Mainly intended for creating short lists in eg. the REPL
"""
function list(v::Vararg{T}) where {T}
  # FIXME: recursive
  # NOTE: tällä _list-metodilla tää on type stable, mutta rekursiivinen...
  return _list(Nil{T}(), reverse(v)...)

  ## NOTE: en saanu tästä type stablea järkevästi. Pitäis ehkä tätä "function barrier accumulation"-kikkaa käyttää? Toisaalta en tiiä onks sillä kauheasti väliä, tätä funktiota ei varmaan juuri käytetä muuten ku tyyliin REPL:issä tai muuten vaan tosi lyhkästen listien luontiin
  ## "function barrier accumulation": https://discourse.julialang.org/t/tail-call-optimization-and-function-barrier-based-accumulation-in-loops/25831
  # T = eltype(v)
  # l = Nil{T}()
  # for x in reverse(v)
  #   l = Cons(x, l)
  # end
  # l
end

function list(v::Any...)
  # FIXME: recursive
  # NOTE: tällä _list-metodilla tää on type stable, mutta rekursiivinen...
  return _list(Nil{Undef}(), reverse(v)...)

  ## NOTE: en saanu tästä type stablea järkevästi. Pitäis ehkä tätä "function barrier accumulation"-kikkaa käyttää? Toisaalta en tiiä onks sillä kauheasti väliä, tätä funktiota ei varmaan juuri käytetä muuten ku tyyliin REPL:issä tai muuten vaan tosi lyhkästen listien luontiin
  ## "function barrier accumulation": https://discourse.julialang.org/t/tail-call-optimization-and-function-barrier-based-accumulation-in-loops/25831
  # T = eltype(v)
  # l = Nil{T}()
  # for x in reverse(v)
  #   l = Cons(x, l)
  # end
  # l
end

List{T}(vs...) where {T} = _list(Nil{T}(), reverse(map(as(T), vs))...)

export List, AbstractList, Nil, Cons

Base.show(io::IO, ::Nil) = print(io, "Nil")
function Base.show(io::IO, ::MIME"text/plain", c::AbstractList{T}) where {T}
  elems = c |> collect
  _T = @isdefined(T) ? T : Any
  print(io, "List{", _T, "}(")
  print(io, elems |> mapper(repr) |> @<(join(',')))
  return print(io, ')')
end

function Base.show(io::IO, c::AbstractList)
  elems = c |> collect
  print(io, "List(")
  print(io, elems |> mapper(repr) |> @<(join(',')))
  return print(io, ')')
end

Base.:(==)(@nospecialize(_::Nil), @nospecialize(_::Nil))  = true
Base.:(==)(@nospecialize(_::Cons), @nospecialize(_::Nil)) = false
Base.:(==)(@nospecialize(_::Nil), @nospecialize(_::Cons)) = false
Base.:(==)(a::AbstractArray, @nospecialize(_::Nil))       = isempty(a)
Base.:(==)(@nospecialize(_::Nil), a::AbstractArray)       = isempty(a)
@inline Base.:(==)(x::Cons, y::AbstractArray)             = x |> collect == y
@inline Base.:(==)(x::AbstractArray, y::Cons)             = x == y |> collect
@inline Base.:(==)(x::Cons, y::Cons)                      = x |> collect == y |> collect
# FIXME: less inefficient comparisons

# Base.convert(::Type{List{T}}, ::Nil{Undef}) where {T} = Nil{T}()

Base.length(@nospecialize(_::Nil)) = 0
# Base.length(@nospecialize(xs::Cons{<:Any,<:Any,<:Nil})) = 1
"""
    length(xs::List)

Returns the length of `xs`.

ATTN: O(n) complexity
"""
Base.length(@nospecialize(xs::Cons)) = 1 + length(xs.tail)

# FIXME: recursive
_accum(::Nil, acc) = acc
_accum(l::Cons, acc::AbstractList) = _accum(l.tail, Cons(l.head, acc))

# function Base.reverse(l::Cons{Head,Tail}) where {Head,Tail}
#   _accum(l, Nil{Tail}())
# end
# FIXME: recursive
Base.reverse(l::Cons) = _accum(l, Nil{Undef}())

# FIXME: recursive
Base.cat(a::AbstractList, b::AbstractList) = _accum(reverse(a), b)

"""
    2:(1:nil)

Shortcut for `Cons(2, Cons(1, nil))`.

## ATTN: `3:2:1:nil` won't do what you'd expect, use `3:(2:(1:nil))`, or better yet `List(3,2,1)`
"""
(::Colon)(x, xs::AbstractList) = Cons(x, xs)
# TODO: support 3:2:1:Nil() ??
## In [6]: 3:2:1:Nil()
## List{StepRange{Int64, Int64}}(3:2:1)

# FIXME: bit ugly to override StaticArrays.push & pop when List doesn't have static length, but meh. Gets rid of warnings about ambiguity
StaticArrays.push(xs::AbstractList, x) = Cons(x, xs)
StaticArrays.pop(xs::Cons) = xs.tail
StaticArrays.pop(@nospecialize(_::Nil)) = error("Cannot pop from empty List")

maybe_pop(xs::Cons) = Just(pop(xs))
maybe_pop(@nospecialize(_::Nil)) = none

head(xs::Cons) = xs.head
head(@nospecialize(_::Nil)) = error("Cannot take head of empty List")
Base.tail(xs::AbstractList) = pop(xs)

maybe_head(xs::Cons) = Just(xs.head)
maybe_head(@nospecialize(_::Nil)) = none
maybe_tail(xs::Cons) = Just(xs.tail)
maybe_tail(@nospecialize(_::Nil)) = none

Base.first(xs::AbstractList) = head(xs)
# Base.last(xs::Cons) = @match xs begin
#   Cons(head, ::Nil) => head
#   Cons(_, tail::Cons) => last(tail)
# end
# Base.last(@nospecialize(_::Nil)) = error("Cannot last from empty List")

export push, pop, head, tail, maybe_pop, maybe_tail, list

Accessors.insert(l::AbstractList, ::typeof(head), x)         = Cons(x, l)
Accessors.insert(l::AbstractList, ::typeof(Base.first), x)   = Cons(x, l)
Accessors.delete(l::Cons, ::typeof(head))                    = l.tail
Accessors.delete(l::Cons, ::typeof(Base.first))              = l.tail
Accessors.delete(@nospecialize(::Nil), ::typeof(head))       = error("Cannot delete from empty List")
Accessors.delete(@nospecialize(::Nil), ::typeof(Base.first)) = error("Cannot delete from empty List")

# TODO: laajempi Accessors.insert -tuki 
## ks. @inline function insert(obj::AbstractVector, l::IndexLens{<:Tuple{UnitRange}}, val)

Base.iterate(@nospecialize(l::AbstractList), @nospecialize(_ = nil)) = nothing
Base.iterate(l::Cons, state::Cons=l) = (state.head, state.tail)
Base.eltype(::Type{<:AbstractList{<:T}}) where {T} = @isdefined(T) ? T : Any

@testitem "List" begin
  using Accessors
  using Musica: nil, __enable_debug
  __enable_debug() do

    # homogeous list
    let lst = list(3, 2, 1)
      @test lst === 3:(2:(1:nil))

      @test lst isa AbstractList{Int}

      @test length(lst) == 3
      @test length(1:nil) == 1
      @test length(nil) == 0
      @test eltype(lst) == Int

      # NOTE: return type is Union{Nil{T},Cons{T}} / ListUnion{T}, hence @test_inferret
      @test Musica.@test_inferret(pop(lst)) == list(2, 1)
      @test @inferred(head(lst)) == 3
      @test @inferred(push(lst, 4)) == list(4, 3, 2, 1)

      @test (@delete head(lst)) == list(2, 1)
      @test (@delete Base.first(lst)) == list(2, 1)
      @test (@insert head(lst) = 4) == list(4, 3, 2, 1)
      @test (@insert Base.first(lst) = 4) == list(4, 3, 2, 1)
    end

    let lst1 = 3:("a":(true:nil)), lst2 = list(3, "a", true)
      @test lst1 == lst2
    end

    # heterogenous lists with a small amount of "simple enough" types should have a Union eltype. Right now the limit is 3 types.
    # TODO[low-prio]: this'll bork if eg. Core.Compiler.issimpleenoughtype changes. Make it not bork.
    let lst = list(3, "a", true)
      @debug :lst lst typeof(lst) |> supertype
      @test lst isa AbstractList{Union{Int,String,Bool}}
      @test Musica.@test_inferret(tail(lst)) == list("a", true)

      @test Musica.@test_inferret(head(tail(lst))) == "a"

      let lst2 = 55.5:lst
        @debug :lst2 lst2 typeof(lst2)
        @test eltype(lst2) === Any
      end
    end
    let lst = list(true, "a") # true:("a":Nil())
      # @debug typeof(lst) |> supertype
      @test lst isa AbstractList{Union{Bool,String}}
    end
  end
end

@inline maybe_peel(iter) = _maybe_peel_td(iter)

@inline function _maybe_peel_td(iter)
  head = iter |> Take(1) |> collect
  (head == []) && return none
  return Just((head, iter |> Drop(1)))
end

function _maybe_peel_it(iter)
  peeled_rest = Iterators.peel(iter)
  peeled_rest == nothing && return none
  head::eltype(iter), rest = Try.@? peeled_rest

  return Just((head, Iterators.drop(iter, 1)))
end

"""
    KeepSome()

Like `Transducers.KeepSomething` but supports `Just` / `None` in addition to `Some` / `Nothing`
"""
struct KeepSome <: Transducers.Transducer end

Transducers.isexpansive(::KeepSome) = false

function Transducers.next(rf::Transducers.R_{KeepSome}, result, iinput)
  return iinput == nothing ? result :
         Transducers.next(Transducers.inner(rf), result, some(iinput))
end

"""
collects `src` into `dest`. Mutates `dest`. Will collect at most `length(dest)` elements.

## FIXME: will bork if `dest` uses any other type than `Int`s for indexing, or if its indices don't run densely from `1:length(dest)`
"""
@inline @inline collect_into!(dest, src) =
  foldxl(src |> Enumerate(); init=dest) do acc, (idx, a)
    @inline
    @inbounds acc[idx] = a
    return acc
  end

export collect_into!

@inline pushing_into!(dest::Type, src) =
  foldxl(push!! |> whencombine(append!!) |> wheninit(dest), src)

export pushing_into!

module Similarity
#WIP: similarity scores. https://github.com/zgornel/StringAnalysis.jl ?
end

module Iter
using ..Musica: @ifsomething, Optional, none, @some, right, mapper, OptOrValue
using Accessors, AccessorsExtra, TypeUtils, TestItems, Try, TryExperimental, StaticArrays
"""
    Rest(iterable)
    Rest(iterable, itr_state)
    Rest{ItrState}(iterable)

Like `Iterators.Rest` but type stable; where `Iterators.rest([1, 2])` will return `[1, 2]`, `Iter.Rest([1, 2])` will return an `Iter.Rest`.

```jldoctest
julia> Iterators.rest([1, 2]) |> typeof
Vector{Int64} (alias for Array{Int64, 1})

julia> Iter.Rest([1, 2]) |> typeof
Musica.Iter.Rest{Int64, Vector{Int64}}
```
"""
struct Rest{ItrState,Iterable}
  iterable::Iterable
  itr_state::Optional{ItrState}

  Rest{ItrState,Iterable}(iterable, itr_state) where {ItrState,Iterable} =
    new{ItrState,Iterable}(iterable, itr_state)
  # function (::Type{T})(
  #   iterable,
  #   itr_state=none,
  # ) where {Iterable,ItrState,Rest{ItrState,Iterable} <: T <: Rest}
  #   @debug :Rest @isdefined(Iterable) @isdefined(ItrState)
  #   let Iterable = @isdefined(Iterable) ? Iterable : typeof(iterable),
  #     ItrState =
  #       @isdefined(ItrState) ? ItrState :
  #       @ifsomething(s -> typeof(s), itr_state, iterable |> itr_state_type)

  #     @debug :Rest iterable Iterable itr_state ItrState
  #     new{ItrState,Iterable}(iterable, itr_state)
  #   end
  # end
end

function Rest(iterable, itr_state::OptOrValue=none)
  let ItrState = @ifsomething(s -> typeof(s), itr_state, iterable |> itr_state_type)
    return Rest{ItrState,Core.Typeof(iterable)}(iterable, itr_state)
  end
end

function Rest{ItrState}(iterable, itr_state::OptOrValue{ItrState}=none) where {ItrState}
  return Rest{ItrState,Core.Typeof(iterable)}(iterable, itr_state)
end

# so that `Rest(rest::Rest,somestate)` won't unnecessarily re-wrap a `Rest`
Rest(rest::Rest{ItrState,Itr}, itr_state::OptOrValue{ItrState}=none) where {ItrState,Itr} =
  Rest{ItrState,Itr}(rest.iterable, itr_state)

# TODO[low-prio]: less inefficient comparison
Base.:(==)(a::Rest, b::Rest) = isequal(a |> collect, b |> collect)

_try_itr_arg_err(T) =
  Try.Err(ArgumentError(LazyString("no try_itr_state_type defined for type ", T)))
@accessor iterable(r::Rest) = r.iterable
iterable_type(::Type{<:Rest{IS,I} where {IS}}) where {I} = I
iterable_type(r::Rest) = r |> typeof |> iterable_type

try_itr_state_type(T::Type) = _try_itr_arg_err(T)

try_itr_state_type(@nospecialize(T::Type{<:SubArray{<:Any,<:Any,C}})) where {C} =
  Try.@or(try_itr_state_type(C), _try_itr_arg_err(T))
try_itr_state_type(::Type{<:StaticVector{N}}) where {N} = Try.Ok(Tuple{SOneTo{N},Int})
try_itr_state_type(@nospecialize(_::Type{<:Vector})) = Try.Ok(Int)
try_itr_state_type(::Type{<:Rest{IS}}) where {IS} = Try.Ok(IS)

try_itr_state_type(x) = x |> typeof |> try_itr_state_type

"""
    Iter.itr_state_type(T)

Returns the state type in the tuple that would be returned by `iterate(x::T)`. Eg. `itr_state_type(Vector{Bool})` would be `Int` because `iterate(x::Vector{Bool})` returns `Tuple{Bool, Int}`. Throws if no `Iter.itr_state_type` is defined for `T`.

Use `Iter.try_itr_state_type` to return a `Try.Ok` / `Try.Err` instead of throwing.
"""
itr_state_type(x) = x |> try_itr_state_type |> Try.unwrap

itr_state_type_from_call(x) = x |> iterate |> Optional |> mapper(typeof ∘ right)
# map(x -> typeof(right(x)), Optional(iterate(x)))

@inline function Base.iterate(r::Rest{IS,Itr}, state::Optional{IS}=r.itr_state) where {IS,Itr}
  let IterType = approx_iter_type(Itr)
    itr::Union{Nothing,IterType} =
      @ifsomething(state, iterate(r.iterable)) do s
        iterate(r.iterable, s)
      end
    @debug "iterate(r::Rest)" r state IterType itr
    isnothing(itr) && return nothing
    (val, state) = itr
    return (val, convert(Optional{typeof(state)}, state))
  end
end

_rest_iteratorsize(@nospecialize(_)) = Base.SizeUnknown()
_rest_iteratorsize(::Base.IsInfinite) = Base.IsInfinite()
# TODO: figure out the length somehow, for some cases?
Base.IteratorSize(::Type{<:Rest{I}}) where {I} = _rest_iteratorsize(Base.IteratorSize(I))

Base.IteratorEltype(::Type{<:Rest{ItrState,Iterable} where {ItrState}}) where {Iterable} =
  Base.IteratorEltype(Iterable)
Base.eltype(::Type{<:Rest{ItrState,Iterable} where {ItrState}}) where {Iterable} = eltype(Iterable)
#Base.length(rest::Rest) = length(rest.iterable)
#Base.axes(rest::Rest, d) = axes(rest.iterable, d)
#Base.axes(rest::Rest) = axes(rest.iterable)
#Base.size(rest::Rest, d) = size(rest.iterable, d)
#Base.size(rest::Rest) = size(rest.iterable)

@testitem "Iter.Rest" begin
  # Musica.__enable_debug("Main", "Musica", "Musica.Iter") do

  let it = Iter.Rest(Bool[1, 0])
    @test Test.@inferred(Iter.Rest(Bool[1, 0])) |> collect == it |> collect
    @test Test.@inferred(Iter.Rest(Bool[1, 0]) |> collect) == it |> collect
    @test Test.@inferred(Iter.Rest(Iter.Rest(Bool[1, 0]), Just(2))) |> collect ==
          Iter.Rest(it, Just(2)) |> collect

    @test [x for x in it] == [1, 0]
    @test Iter.iterable_type(it) == Vector{Bool}
    @test Iter.itr_state_type(it) == Int
    let it2 = Iter.Rest(it, it |> iterate |> Musica.right)
      @test [x for x in it2] == [0]
      @test it2 |> Iter.iterable_type == it |> Iter.iterable_type
      @test it2 |> Iter.itr_state_type == it |> Iter.itr_state_type
      @test Iter.iterable_type(it2) == Vector{Bool}
      @test Iter.itr_state_type(it2) == Int
    end
  end
  # end
end

struct WithNextState{It}
  itr::It
end

Base.IteratorSize(::Type{<:WithNextState{It}}) where {It} = Base.IteratorSize(It)
Base.IteratorEltype(::Type{<:WithNextState{It}}) where {It} = Base.IteratorEltype(It)
# NOTE: `approx_iter_type(T)` will generally be `Union{Nothing, Tuple{Elt,State}}`. `Base.nonnothingtype` gets rid of the `Nothing` if present
Base.eltype(::Type{<:WithNextState{It}}) where {It} = approx_iter_type(It) |> Base.nonnothingtype
Base.length(ws::WithNextState) = length(ws.itr)
Base.axes(ws::WithNextState, d) = axes(ws.itr, d)
Base.axes(ws::WithNextState) = axes(ws.itr)
Base.size(ws::WithNextState, d) = size(ws.itr, d)
Base.size(ws::WithNextState) = size(ws.itr)

function Base.iterate(ws::WithNextState, its...)
  let iter_res = iterate(ws.itr, its...)
    isnothing(iter_res) && return nothing
    (val, state) = iter_res
    return ((val, state), state)
  end
end

@testitem "Iter.WithNextState" begin
  let it = Iter.WithNextState(Bool[1, 0])
    @test @inferred(it |> collect) == [(1, 2), (0, 3)]
    @test Musica.@test_inferret(iterate(it)) == ((1, 2), 2)
  end
end

# NOTE: copied from stdlib Iterators
# Try to find an appropriate type for the (value, state tuple),
# by doing a recursive unrolling of the iteration protocol up to
# fixpoint.
approx_iter_type(itrT::Type) = _approx_iter_type(itrT, Base._return_type(iterate, Tuple{itrT}))
# Not actually called, just passed to return type to avoid
# having to typesplit on Nothing
function _doiterate(itr, valstate::Union{Nothing,Tuple{Any,Any}})
  valstate === nothing && return nothing
  val, st = valstate
  return iterate(itr, st)
end
function _approx_iter_type(itrT::Type, vstate::Type)
  vstate <: Union{Nothing,Tuple{Any,Any}} || return Any
  vstate <: Union{} && return Union{}
  itrT <: Union{} && return Union{}
  nextvstate = Base._return_type(_doiterate, Tuple{itrT,vstate})
  return (nextvstate <: vstate) || (nextvstate <: Nothing) ? vstate : Any
end

end

export Iter