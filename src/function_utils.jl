using Transducers, TestItems, MacroTools, Static, Try, TryExperimental, Tricks
using FunctionWrappers: FunctionWrapper as Fn

"""
    repeated(fn, times)

Compose `fn` with itself `times` times
"""
@inline function repeated(fn, times)::Function
  repeated_for(fn, times)
end

@testitem "repeated" begin
  _fn(x) = 2x
  @test Musica.repeated_compose(_fn, 5)(5) == Musica.repeated_iter(_fn, 5)(5) ==
        Musica.repeated_for(_fn, 5)(5)
end

# HUOM: repeated_compose:n palauttama funkkari on reilusti nopeampi ku repeated_fold:in, mutta
# sen composen kasaaminen kestää ***1000x*** kauemmin esim. jos times=30
@inline repeated_compose(fn, times) = ∘(fill(fn, times)...)

# # foldl takes a fn (acc, x). (fn ∘ left) is (acc,_) -> fn(acc)
# # this is basically just fn composed with itself `times` times (fn ∘ fn ∘ ... )
@inline repeated_fold(fn, times) = (input) -> (@inline; foldl((fn ∘ left), 1:times; init=input))
@inline repeated_iter(fn, times) =
  inp -> (@inline; 1:times+1 |> Iterated(fn, inp) |> TakeLast(1) |> collect |> only)

@inline function repeated_for(fn, times)
  input -> begin
    @inline
    let out = input
      for _ in 1:times
        out = fn(out)
      end
      out
    end
  end
end

const ArgHead = :BindHead
const ArgTail = :BindTail

"""
Like `Base.Fix1` and `Base.Fix2` but supports binding / fixing an arbitrary number of arguments starting from the first or the last, . See the `@<` and `@>` macros
"""
struct BoundCall{InitArgPos,InitArg,F,KW} <: Function
  f::F
  arg::InitArg
  kw::KW

  function BoundCall{InitArgPos,F}(
    f::F,
    x,
    kwargs,
  ) where {InitArgPos,F}
    new{InitArgPos,Core.Typeof(x),F,typeof(kwargs)}(f, x, kwargs)
  end
end

BoundCall{ArgPos}(f, x; kw...) where {ArgPos} =
  BoundCall{ArgPos,Core.Typeof(f)}(f, x, kw)

BoundCall{ArgPos}(f, x::Vararg{Any,N}; kw...) where {ArgPos,N} =
  BoundCall{ArgPos,Core.Typeof(f)}(f, x, kw)

Base.show(io::IO, b::BoundCall) =
  print(io, _stringify_bound_call(b)...)

function Base.show(io::IO, ::MIME"text/plain", b::BoundCall)
  print(io, "BoundCall(")
  print(io, b, ')')
end

const _emptyKW::typeof(pairs((;))) = pairs((;))
const _EmptyKW = _emptyKW |> typeof

"""
a shortcut for a `BoundCall` with >1 arguments, ie. ones where `InitArg` is a tuple
"""
const BoundCWTuple{InitArgPos} = BoundCall{InitArgPos,InitArg} where {InitArg<:Tuple}

"""
Only call `merge` if both parameters are non-empty, otherwise just return the non-empty param
"""
@inline _merge_nonempty(d, other) = merge(d, other)
@inline _merge_nonempty(d, ::_EmptyKW) = d
@inline _merge_nonempty(::_EmptyKW, d) = d
@inline _merge_nonempty(::_EmptyKW, ::_EmptyKW) = _emptyKW

@inline (f::BoundCall{ArgHead})(ys...) =
  f.f(f.arg, ys...; f.kw...)
@inline (f::BoundCWTuple{ArgHead})(ys...) =
  f.f(f.arg..., ys...; f.kw...)

@inline (f::BoundCall{ArgTail})(xs...) = f.f(xs..., f.arg; f.kw...)
@inline (f::BoundCWTuple{ArgTail})(xs...) =
  f.f(xs..., f.arg...; f.kw...)

_stringify_args(::Tuple{}) = ""
_stringify_args(args...) = join(map(repr, args), ",")
_stringify_args(args) = repr(args)
_stringify_kws(kws) = ";" * join(["$(x.first)=$(x.second)" for x in kws], ",")
_stringify_kws(::_EmptyKW) = ""

_stringify_unbound_param(::Val{ArgHead}, name, ::Tuple{}) = name
_stringify_unbound_param(::Val{ArgTail}, name, ::Tuple{}) = name
_stringify_unbound_param(::Val{ArgHead}, name, @nospecialize(args)) = string(", ", name)
_stringify_unbound_param(::Val{ArgTail}, name, @nospecialize(args)) = string(name, ", ")

function _stringify_bound_call(bc::BoundCall{ArgHead})
  pname = _param_name_for(bc)

  ('(', pname, ") -> ", string(bc.f), "(",
    _stringify_args(bc.arg),
    _stringify_unbound_param(Val{ArgHead}(), pname, bc.arg),
    _stringify_kws(bc.kw), ")")
end

function _stringify_bound_call(bc::BoundCall{ArgTail})
  pname = _param_name_for(bc)

  ('(', pname, ") -> ", string(bc.f), "(",
    _stringify_unbound_param(Val{ArgTail}(), pname, bc.arg),
    _stringify_args(bc.arg),
    _stringify_kws(bc.kw), ")")
end

const _metasynt_names::NTuple{16,String} =
  (
    "foo",
    "bar",
    "baz",
    "qux",
    "corge",
    "grault",
    "garply",
    "waldo",
    "alice",
    "eve",
    "bob",
    "xyzzy",
    "spam",
    "eggs",
    "ham",
    "plugh",
  )

const _metasynt_args::typeof(_metasynt_names) = map(x -> x * "...", _metasynt_names)

_param_name_for(x) =
  let v = x |> objectid, _metasyn_len = length(_metasynt_args)
    _metasynt_args[1+(v%_metasyn_len)]
  end

@testitem "BoundCall" begin
  using Musica: BoundCall, ArgHead, ArgTail
  fn(a, b; c=3, d=4) = a / (b - c)d
  let bfn = BoundCall{ArgHead}(fn, 1)
    @test @inferred(bfn(2)) ==
          fn(1, 2)
  end

  let bfn = BoundCall{ArgHead}(fn, 1, 2)
    @test @inferred(bfn()) ==
          fn(1, 2)
  end

  let bfn = BoundCall{ArgHead}(fn)
    @test @inferred(bfn(1, 2)) ==
          fn(1, 2)
  end

  let bfn = BoundCall{ArgTail}(fn, 2)
    @test @inferred(bfn(1)) ==
          fn(1, 2)
  end

  let bfn = BoundCall{ArgTail}(fn, 1, 2)
    @test @inferred(bfn()) ==
          fn(1, 2)
  end

  let bfn = BoundCall{ArgTail}(fn)
    @test @inferred(bfn(1, 2)) ==
          fn(1, 2)
  end
end

"""
    bound = @> fn(a,b)
    bound(c, d) == fn(a, b, c, d)

Bind a function call (or other callable, such as a type) so that arguments are bound starting from the first (left). The argument must be a function call with at least one argument, and zero or more keyword arguments.

```jldoctest
julia> a = 1;

julia> plus1 = @> +(a);

julia> plus1(2)
3

julia> plus1(2, 3)
6

julia> to_binary_digits = @> digits(Int; base=2, pad=8);

julia> show(to_binary_digits(20))
[0, 0, 1, 0, 1, 0, 0, 0]

julia> fn = (a, b, c, d; kw1, kw2) -> (a + b + c + d)kw1 // kw2;

julia> bound = @> fn(1, 2; kw1=13, kw2=1000);

julia> fn(1, 2, 3, 4; kw1=13, kw2=1000) == bound(3, 4)
true
```
"""
macro >(ex)
  _bound(ex, ArgHead)
end

export @>

"""
    @< fn(a)
    @< fn(a, b)
    @< fn(a; kw=1)

Bind a function call (or other callable, such as a type) so that arguments are bound starting from the tail (right). The argument must be a function call with at least one argument,
and zero or more keyword arguments.

```jldoctest
julia> fn = (a, b, c, d; kw1, kw2) -> (a + b + c + d)kw1 // kw2;

julia> curried = @< fn(3, 40; kw2=1000, kw1=13);

julia> curried(1, 2) == fn(1, 2, 3, 40; kw1=13, kw2=1000)
true
```
"""
macro <(ex)
  _bound(ex, ArgTail)
end

export @<

function _bound(ex, argpos)
  @capture(ex, fn_(args__; kws__) | fn_(args__)) ||
    error("Not used on a function call? Syntax: @> f(a, b; c = 1)")

  fn = esc(fn)
  _args = !isnothing(args) ? map(esc, args) : []
  _kws = !isnothing(kws) ? map(esc, kws) : []

  quote
    Musica.BoundCall{$(QuoteNode(argpos))}($fn, $(_args...), $(_kws...))
  end
end

@testitem "macros" begin
  using StaticArrays, Transducers, Static, MicroCollections
  fn(a, b; c, d=0) = (a - b) * (c + d)

  # pelkkä kw arg
  @test @inferred(@<(fn(; c=5))(12, 2)) == 50

  # pelkkä kw pitäis toimia samalla tavalla sekä @> että @<
  @test @inferred(@>(fn(; c=5))(12, 2)) == 50

  @test @inferred(@>(fn(12; c=5))(2)) == 50

  # testaa että hommat toimii myös konstruktoreiden kanssa. `Dada(n)`ssä `Dada`n tyyppi on `UnionAll` eikä
  # Function
  struct Dada{A,B,C}
    field::Int
  end

  Dada(v) = Dada{Int,Int,Int}(v)
  @test @inferred((@> Dada(5))()) == Dada{Int,Int,Int}(5)

  Base.@constprop :aggressive @inline function _droplast(
    arr::SizedVector{L},
    n,
  ) where {L}
    arr_parent = arr |> parent
    # NOTE: @inbounds is safe here because if n≥L, the slice would just give an empty array/view
    @inbounds begin
      SizedVector{L - n}(@view arr_parent[1:end-n])
    end
  end

  Base.@constprop :aggressive @inline function _droplast2(
    arr,
    n,
  )
    # NOTE: @inbounds is safe here because if n≥L, the slice would just give an empty array/view
    @inbounds begin
      @view arr[1:end-n]
    end
  end
  #! format: off
  const AllowedT = Union{Vector{StaticArraysCore.SizedVector{3,Int64,SubArray{Int64,1,Vector{Int64},Tuple{UnitRange{Int64}},true},},},MicroCollections.UndefVector{Union{},typeof(MicroCollections.default_factory)},}
  #! format: on

  let sv = map(x -> SizedVector{5}(x:x+4 |> collect), 1:5)
    @test(Musica.@test_inferret(sv |> Map(@<(_droplast(static(2)))) |> collect) |> sum |> sum == 60)
  end

  let sv = map(x -> SizedVector{5}(x:x+4 |> collect), 1:5)
    @test(@inferred(Iterators.map(@<(_droplast(static(2))), sv) |> collect) |> sum |> sum == 60)
  end

  @test @inferred(SizedVector{5}(1:5 |> collect) |> @<(_droplast2(2))) ==
        SizedVector{3}(1:3 |> collect)

  let sv = map(x -> SizedVector{5}(x:x+4 |> collect), 1:5)
    @test(@inferred(Iterators.map(x -> _droplast(x, 2), sv) |> collect) |> sum |> sum == 60)
  end
end

"""
    mapper(fn)

Partially applied `map(fn, _)`, returns `x -> map(fn, x)`
"""
@inline mapper(fn) = Base.Fix1(map, fn)
export mapper

_wrapperize(x) = esc(x)

function _wrapperize(expr::Expr)
  if expr.head == :block
    return Expr(:block, _wrapperize.(expr.args)...)
  elseif expr.head == :tuple
    return Expr(:tuple, _wrapperize.(expr.args)...)
  elseif @capture(expr, (inputs__,) -> output_)
    return :(Fn{$(_wrapperize(output)),Tuple{$(_wrapperize.(inputs)...)}})
  elseif @capture(expr, (input_) -> output_)
    return :(Fn{$(_wrapperize(output)),Tuple{$(_wrapperize(input))}})
  elseif @capture(expr, T_{Args__})
    return esc(expr)
  else
    error(
      "I can only handle expressions of the form `(inputs...) -> output`, got $(expr|>Base.remove_linenums!)\n$(sprettyprint_expr(expr|>Base.remove_linenums!))",
    )
  end
end

"""
    (@Fn Vector{Bool} -> UInt)(undigits)
    T = @Fn (Int -> Int) -> Bool
    is_foo::@Fn Any -> Tuple{Bool, Float64} = […]

Palauttaa parametrisoidun funktiotyypin (`Fn`, lyhennetty `FunctionWrapper` koska mikä vitun järki on nimetä se `FunctionWrappers.FunctionWrapper`iksi).

Lähde: https://discourse.julialang.org/t/can-functionwrappers-jl-express-higher-order-functions/66404/4
"""
macro Fn(expr)
  _wrapperize(expr)
end

export @Fn, Fn

@testitem "@Fn" begin
  using Test
  using FunctionWrappers: FunctionWrapper

  let T = @Fn((Vector{Bool}) -> UInt), fn = T(@<(undigits(2)))
    @test @inferred(fn([1, 1, 1])) == 0b111
    @test T == FunctionWrapper{UInt,Tuple{Vector{Bool}}}
  end
end

# TODO: State monad-henkinen viritelmä?
# HOX: ajatus oli, että parserit vois olla state-monadeja, mutta ongelma on että Parser.S tyyppi muuttuu joka askeleella.

# HOX: tää olis siitä hyvä että sit inferenssi olis ihan lapsellisen helppoa ja luultavassti takuuvarmaa.
# https://stackoverflow.com/questions/7734756/scalaz-state-monad-examples
# https://github.com/ulysses4ever/Monads.jl/blob/master/src/Monads.jl
struct State{S,V}
  run::@Fn S -> Tuple{S,V}
end

fntype_output_type(f::Type{<:Fn{Output}}) where {Output} = Type{Output}
fntype_input_type(f::Type{<:Fn{O,In} where {O}}) where {In} = Type{In}

const TryResult = Union{<:Try.Ok,<:Try.Err}

try_lift(x::TryResult) = x
try_lift(@nospecialize(x)) = Try.Ok(x)
try_lift(@nospecialize(x::Exception)) = Try.Err(x)

macro trying(ex)
  _trying(ex, __source__)
end

function _trying(ex, source)
  # TODO: effect inference magic on ex? If compiler says the expression would be a nothrow, could we skip the try/catch completely?
  # That would assume the effect of running ex won't change, though? ¯\_(ツ)_/¯
  @esc ex
  quote
    try
      $try_lift($(ex))
    catch e
      $Try.Err(e)
    end
  end |> MacroTools.flatten |> replace_linenums!(source)
end

export @trying