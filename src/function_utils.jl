using Transducers, TestItems, Test, MacroTools

using Lazy: iterated

@inline _stable_typeof(x) = typeof(x)
@inline _stable_typeof(::Type{T}) where {T} = @isdefined(T) ? Type{T} : DataType

"""
    repeated(fn, times)

Compose `fn` with itself `times` times
"""
@inline function repeated(fn, times)::Function
  if times == 1
    return fn
  end
  # repeated_fold(fn, times)
  # HUOM: exec time on reilusti nopeampi repeated_compose:n lopputuloksella, mutta
  # sen composen kasaaminen (eli repeated_compose(fn,n) kutsu) kestää kauemmin ku mitä
  # repeated_fold

  if times ≤ 20
    repeated_compose(fn, times)
  else
    repeated_iter(fn, times)
  end
end

# HUOM: repeated_compose:n palauttama funkkari on reilusti nopeampi ku repeated_fold:in, mutta
# sen composen kasaaminen kestää ***1000x*** kauemmin esim. jos times=30
@inline repeated_compose(fn, times) = ∘(fill(fn, times)...)

# # foldl takes a fn (acc, x). (fn ∘ _left) is (acc,_) -> fn(acc)
# # this is basically just fn composed with itself `times` times (fn ∘ fn ∘ ... )
@inline repeated_fold(fn, times) = (input) -> (@inline; foldl((fn ∘ _left), 1:times; init=input))
@inline repeated_iter(fn, times) = inp -> (@inline; 1:times+1 |> Iterated(fn, inp) |> TakeLast(1) |> collect |> only)
@inline _left(a, _) = a

######### HUOM: tää Base.Fix:in tuunaus ei välttis oo planeetan paras idea

# """
#     Fix1(fn, x)(y1[, y2[; kwargs...]])
# Make `Base.Fix1` work with functions with arity > 2 and with keyword arguments.

# ```jldoctest
# julia> summer = Base.Fix1(map, +);

# julia> summer([1,2], [3,4])
# 2-element Vector{Int64}:
#  4
#  6
# ```
# """
# (f::Base.Fix1)(ys...; kwargs...) = f.f(f.x, ys...; kwargs...)
# (f::Base.Fix2)(ys...; kwargs...) = f.f(ys..., f.x; kwargs...)

"""
    CurryHead(fn, a)
    CurryHead(fn, a, b)
    CurryHead(fn, a; kw = 1)

Curry a function call so that arguments are bound starting from the first (left). `CurryHead(fn, a)(b, c) == fn(a, b, c)`.

  
```jldoctest
julia> plus1 = CurryHead(+, 1);

julia> plus1(2)
3

julia> plus1(2,3)
6

julia> digger = CurryHead(digits, Int; base=2);

julia> show(digger(20; pad=8))
[0, 0, 1, 0, 1, 0, 0, 0]

julia> show(digger(20))
[0, 0, 1, 0, 1]

julia> fn = (a, b, c, d; kw1, kw2) -> (a + b + c + d)kw1 // kw2;

julia> curried = CurryHead(fn, 1, 2; kw1 = 13);

julia> curried(3, 40; kw2 = 1000)
299//500
```
"""
struct CurryHead{InitArg,F<:Function,KW} <: Function
  f::F
  x::InitArg
  kw::KW

  CurryHead(f::F, x; kwargs...) where {F} = new{_stable_typeof(x),F,_stable_typeof(kwargs)}(f, x, kwargs)
  CurryHead(f::F, x...; kwargs...) where {F} = new{_stable_typeof(x),F,_stable_typeof(kwargs)}(f, x, kwargs)
end

const CurryHeadTup = CurryHead{InitArg} where {InitArg<:Tuple}

# HUOM: turha määritellä esim (f::CurryHead)(y) = f.f(f.x, y; f.kw...), koska funktio parametreilla (y; kw...) näyttää aina rynnivän yli
# kwargittomasta versiosta. Tää taitaa liittyä jotenkin siihen miten kwargit toimii konepellin alla

@inline (f::CurryHead)(y; kw...) = f.f(f.x, y; _merge_nonempty(f.kw, kw)...)
@inline (f::CurryHead)(ys...; kw...) = f.f(f.x, ys...; _merge_nonempty(f.kw, kw)...)

# methods below are used when the value in f.x is a Tuple, ie. when multiple arguments were bound

@inline (f::CurryHeadTup)(y; kw...) = f.f(f.x..., y; _merge_nonempty(f.kw, kw)...)
@inline (f::CurryHeadTup)(ys...; kw...) = f.f(f.x..., ys...; _merge_nonempty(f.kw, kw)...)

struct CurryTail{InitArg,F<:Function,KW} <: Function
  f::F
  x::InitArg
  kw::KW

  CurryTail(f::F, x; kwargs...) where {F} = new{_stable_typeof(x),F,_stable_typeof(kwargs)}(f, x, kwargs)
  CurryTail(f::F, x...; kwargs...) where {F} = new{_stable_typeof(x),F,_stable_typeof(kwargs)}(f, x, kwargs)
end

const CurryTailTup = CurryTail{InitArg} where {InitArg<:Tuple}

@inline (f::CurryTail)(y; kw...) = f.f(y, f.x; _merge_nonempty(f.kw, kw)...)
@inline (f::CurryTail)(ys...; kw...) = f.f(ys..., f.x; _merge_nonempty(f.kw, kw)...)

# methods below are used when the initial value in f.x is a Tuple

@inline (f::CurryTailTup)(y; kw...) = f.f(y, f.x...; _merge_nonempty(f.kw, kw)...)
@inline (f::CurryTailTup)(ys...; kw...) = f.f(ys..., f.x...; _merge_nonempty(f.kw, kw)...)

const _EmptyKW = Base.Pairs{Symbol,Union{},Tuple{},NamedTuple{(),Tuple{}}}
const _emptyKW = pairs((;))

"Only call `merge` if both parameters are non-empty, otherwise just return the non-empty param"
@inline _merge_nonempty(d::AbstractDict, other::AbstractDict) = merge(d, other)
@inline _merge_nonempty(d::AbstractDict, ::_EmptyKW) = d
@inline _merge_nonempty(::_EmptyKW, d::AbstractDict) = d
@inline _merge_nonempty(::_EmptyKW, ::_EmptyKW) = _emptyKW

macro ©(ex)
  _curried(ex, :CurryHead)
end

"""
    @> fn(a)
    @> fn(a, b)
    @> fn(a; kw=1)

Curry a function call so that arguments are bound starting from the first (left). The argument must be a function call with at least one argument, and zero or more keyword arguments.

    curried = @> fn(a,b); curried(c, d) == fn(a, b, c, d)

See [`CurryHead`](@ref).

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

julia> curried = @> fn(1, 2; kw1 = 13);

julia> curried(3, 4; kw2 = 1000) # same as fn(1, 2, 3, 4; kw1 = 13, kw2 = 1000)
13//100

```
julia> fn(1, 2, 3, 4; kw1 = 13, kw2 = 1000) == curried(3, 4; kw2 = 1000)
true
"""
macro >(ex)
  _curried(ex, :CurryHead)
end

macro £(ex)
  _curried(ex, :CurryTail)
end

"""
@< fn(a)
@< fn(a, b)
@< fn(a; kw=1)

Convenience macro for constructing a [`CurryTail`](@ref). The argument must be a function call with at least one argument, 
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
  _curried(ex, :CurryTail)
end

function _curried(ex, Constructor)
  @capture(ex, fn_(args__; kws__) | fn_(args__)) || error("Not used on a function call? Syntax: @> f(a, b; c = 1)")
  if length(args) == 0
    error("Function call had no arguments. Syntax: @> f(a, b; c = 1)")
  end

  # @debug fn args kws

  fn = esc(fn)
  args = map(esc, args)
  isnothing(kws) ? kws = Any[] : kws = map(esc, kws)

  # @debug "after esc" fn args kws

  quote
    $Constructor($fn, $(args...); $(kws...))
  end
end

export CurryHead, @©, @£, @>, @<