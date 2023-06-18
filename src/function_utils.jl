using Transducers, TestItems, Test, MacroTools

"""
    repeated(fn, times)

Compose `fn` with itself `times` times
"""
@inline function repeated(fn, times)::Function
  # if times == 1
  #   return fn
  # end
  # repeated_fold(fn, times)
  # HUOM: exec time on reilusti nopeampi repeated_compose:n lopputuloksella, mutta
  # sen composen kasaaminen (eli repeated_compose(fn,n) kutsu) kestää kauemmin ku mitä
  # repeated_fold

  repeated_iter(fn, times)

  # if times ≤ 10
  #   repeated_compose(fn, times)
  # else
  #   repeated_iter(fn, times)
  # end
end

@testitem "repeated" begin
  _fn(x) = 2x
  @test Musica.repeated_compose(_fn, 5)(5) == Musica.repeated_iter(_fn, 5)(5)
end

# HUOM: repeated_compose:n palauttama funkkari on reilusti nopeampi ku repeated_fold:in, mutta
# sen composen kasaaminen kestää ***1000x*** kauemmin esim. jos times=30
@inline repeated_compose(fn, times) = ∘(fill(fn, times)...)

# # foldl takes a fn (acc, x). (fn ∘ _left) is (acc,_) -> fn(acc)
# # this is basically just fn composed with itself `times` times (fn ∘ fn ∘ ... )
@inline repeated_fold(fn, times) = (input) -> (@inline; foldl((fn ∘ _left), 1:times; init=input))
@inline repeated_iter(fn, times) = inp -> (@inline; 1:times+1 |> Iterated(fn, inp) |> TakeLast(1) |> collect |> only)

@inline _left(a, _) = a

const ArgHead = Val{:BindHead}
const ArgTail = Val{:BindTail}
const ArgPos = Union{ArgHead,ArgTail}

struct BoundCall{InitArgPos<:ArgPos,InitArg,F<:Function,KW} <: Function
  f::F
  arg::InitArg
  kw::KW

  BoundCall{InitArgPos}(f::F, x; kwargs...) where {InitArgPos,F} = new{InitArgPos,_stable_typeof(x),F,_stable_typeof(kwargs)}(f, x, kwargs)
  BoundCall{InitArgPos}(f::F, x...; kwargs...) where {InitArgPos,F} = new{InitArgPos,_stable_typeof(x),F,_stable_typeof(kwargs)}(f, x, kwargs)
end

# TODO FIXME: Base.show BoundCall sekä tyypille että valuelle. Nää tyypit rupee muuten oleen aika villejä: Union{Musica.Parsing.var"#2#4"{Tuple{Musica.BoundCall{Val{:BindHead}, State{Vector{Bool}=Nothing,Vector{Bool}}, Exact{Vector{Bool}}, Base.Pairs{Symbol, Union{}, Tuple{}, NamedTuple{(), Tuple{}}}}}}, 

const BoundCallWTuple{InitArgPos} = BoundCall{InitArgPos,InitArg} where {InitArg<:Tuple}

@inline (f::BoundCall{ArgHead})(y; kw...) = f.f(f.arg, y; _merge_nonempty(f.kw, kw)...)
@inline (f::BoundCall{ArgHead})(ys...; kw...) = f.f(f.arg, ys...; _merge_nonempty(f.kw, kw)...)
@inline (f::BoundCallWTuple{ArgHead})(y; kw...) = f.f(f.arg..., y; _merge_nonempty(f.kw, kw)...)
@inline (f::BoundCallWTuple{ArgHead})(ys...; kw...) = f.f(f.arg..., ys...; _merge_nonempty(f.kw, kw)...)

@inline (f::BoundCall{ArgTail})(x; kw...) = f.f(x, f.arg; _merge_nonempty(f.kw, kw)...)
@inline (f::BoundCall{ArgTail})(xs...; kw...) = f.f(xs..., f.arg; _merge_nonempty(f.kw, kw)...)
@inline (f::BoundCallWTuple{ArgTail})(x; kw...) = f.f(x, f.arg...; _merge_nonempty(f.kw, kw)...)
@inline (f::BoundCallWTuple{ArgTail})(xs...; kw...) = f.f(xs..., f.arg...; _merge_nonempty(f.kw, kw)...)


@testitem "BoundCall" begin
  using Musica: BoundCall, ArgHead, ArgTail
  fn(a, b; c=3, d) = a / (b - c)d

  let bfn = BoundCall{ArgHead}(fn, 1)
    @test bfn(2; d=4) == fn(1, 2; d=4)
    @test bfn(2; c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgHead}(fn, 1, 2)
    @test bfn(;d=4) == fn(1, 2; d=4)
    @test bfn(c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgHead}(fn)
    @test bfn(1, 2; d=4) == fn(1, 2; d=4)
    @test bfn(1, 2; c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgTail}(fn, 2)
    @test bfn(1; d=4) == fn(1, 2; d=4)
    @test bfn(1; c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgTail}(fn, 1, 2)
    @test bfn(d=4) == fn(1, 2; d=4)
    @test bfn(c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgTail}(fn)
    @test bfn(1, 2; d=4) == fn(1, 2; d=4)
    @test bfn(1, 2; c=30, d=40) == fn(1, 2; c=30, d=40)
  end
end

"""
HOX: tulee outo herja REPL:iin jos tekee näin: 

    @inline (f::_BoundCallHead{<:Tuple})(y; kw...) = f.f(f.x..., y; _merge_nonempty(f.kw, kw)...)

    @inline (f::_BoundCallHead{<:Tuple})(ys...; kw...) = f.f(f.x..., ys...; _merge_nonempty(f.kw, kw)...)
      #=
      ┌ Warning: skipping callee #_#157 (called by nothing) due to UndefRefError()
      └ @ LoweredCodeUtils ~/.julia/packages/LoweredCodeUtils/30gbF/src/signatures.jl:292
      =#


KYS: miks toi herjaa kun taas `const _BoundCallHeadTup = _BoundCallHead{InitArgs} where {InitArgs<:Tuple}`-aliaksella kaikki menee jees, vaikka ton aliaksen pitäis olla käytännössä sama:

    julia> Musica._BoundCallHead{<:Tuple}
    Main.Musica.BoundCall{Val{:CurryHead}, var"#s257", F} where {var"#s257"<:Tuple, F}

    julia> Musica._BoundCallHeadTup
    Main.Musica.BoundCall{Val{:CurryHead}, InitArgs, F} where {InitArgs<:Tuple, F}

"""

const _EmptyKW = Base.Pairs{Symbol,Union{},Tuple{},NamedTuple{(),Tuple{}}}
const _emptyKW = pairs((;))

"Only call `merge` if both parameters are non-empty, otherwise just return the non-empty param"
@inline _merge_nonempty(d::AbstractDict, other::AbstractDict) = merge(d, other)
@inline _merge_nonempty(d::AbstractDict, ::_EmptyKW) = d
@inline _merge_nonempty(::_EmptyKW, d::AbstractDict) = d
@inline _merge_nonempty(::_EmptyKW, ::_EmptyKW) = _emptyKW

macro ©(ex)
  _bound(ex, :BindHead)
end

"""
    @> fn(a)
    @> fn(a, b)
    @> fn(a; kw=1)

Bind a function call so that arguments are bound starting from the first (left). The argument must be a function call with at least one argument, and zero or more keyword arguments.

    bound = @> fn(a,b); bound(c, d) == fn(a, b, c, d)

See [`BoundCall`](@ref).

```jldoctest
julia> a = 1; plus1 = @> +(a);

julia> plus1(2)
3

julia> plus1(2, 3)
6

julia> to_binary_digits = @> digits(Int; base=2);

julia> show(to_binary_digits(20; pad=8))
[0, 0, 1, 0, 1, 0, 0, 0]

julia> show(to_binary_digits(20))
[0, 0, 1, 0, 1]

julia> fn = (a, b, c, d; kw1, kw2) -> (a+b+c+d)kw1 // kw2;

julia> bound = @> fn(1, 2; kw1 = 13);

julia> bound(3, 4; kw2 = 1000) # same as fn(1, 2, 3, 4; kw1 = 13, kw2 = 1000)
13//100

```
julia> fn(1, 2, 3, 4; kw1 = 13, kw2 = 1000) == bound(3, 4; kw2 = 1000)
true
"""
macro >(ex)
  _bound(ex, :BindHead)
end

macro £(ex)
  _bound(ex, :BindTail)
end

"""
@< fn(a)
@< fn(a, b)
@< fn(a; kw=1)

Bind a function call so that arguments are bound starting from the tail (right). The argument must be a function call with at least one argument, 
and zero or more keyword arguments.

```jldoctest
julia> fn = (a, b, c, d; kw1, kw2) -> (a+b+c+d)kw1 // kw2;

julia> curried = @< fn(3, 40; kw2 = 1000);

julia> curried(1, 2; kw1 = 13) # same as fn(1, 2, 3, 40; kw1 = 13, kw2 = 1000)
299//500

julia> fn(1, 2, 3, 40; kw1 = 13, kw2 = 1000) == curried(1, 2; kw1 = 13)
true
```

"""
macro <(ex)
  _bound(ex, :BindTail)
end

function _bound(ex, argpos)
  @capture(ex, fn_(args__; kws__) | fn_(args__)) || error("Not used on a function call? Syntax: @> f(a, b; c = 1)")
  if length(args) == 0 && length(kws) == 0
    error("Function call had no regular or keyword arguments. Syntax: @> f(a, b; c = 1)")
  end

  # @debug fn args kws

  fn = esc(fn)
  args = map(esc, args)
  isnothing(kws) ? kws = Any[] : kws = map(esc, kws)

  quote
    Musica.BoundCall{Val{$(QuoteNode(argpos))}}($fn, $(args...); $(kws...))
  end
end

"""
    @x 2x # expands to x -> 2x

```jldoctest
julia> (@x 2x)(4)
8
```
"""
macro x(ex)
  :($(esc(:x)) -> $(esc(ex)))
end


@testitem "macros" begin
  # TODO FIXME: curry + UnionAll-tyypin tyyppiparametriton konstruktori
  #= 
    struct ZeroPadded{PadLen,E,T<:AbstractVector{E}} <: AbstractVector{E}
      coll::T
      _coll_len::Int
      function ZeroPadded{PL,E,T}(coll) where {PL,E,T}
        @info coll
        @assert length(coll) ≤ PL "length(coll) $(length(coll)) wasn't ≤ PL ($PL)"
        new{PL,E,T}(coll, length(coll))
      end
    end

    ZeroPadded(a, n) = ZeroPadded{n,Base.eltype(a),typeof(a)}(a)

    @test @<(ZeroPadded(4))([1,2]).coll == ZeroPadded([1,2], 4).coll =#

  fn(a, b; c) = (a - b)c

  # pelkkä kw arg
  @test @<(fn(; c=5))(12, 2) == 50

  # pelkkä kw pitäis toimia samalla tavalla sekä @> että @<
  @test @>(fn(; c=5))(12, 2) == 50

  @test @>(fn(12))(2; c=5) == 50
end

@inline _stable_typeof(x) = typeof(x)
@inline _stable_typeof(::Type{T}) where {T} = @isdefined(T) ? Type{T} : DataType

export @©, @£, @>, @<, @x