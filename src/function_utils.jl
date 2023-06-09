using Transducers, TestItems, MacroTools

"""
    repeated(fn, times)

Compose `fn` with itself `times` times
"""
@inline function repeated(fn, times)::Function
  repeated_for(fn, times)
end

@testitem "repeated" begin
  _fn(x) = 2x
  @test Musica.repeated_compose(_fn, 5)(5) == Musica.repeated_iter(_fn, 5)(5) == Musica.repeated_for(_fn, 5)(5)
end

# HUOM: repeated_compose:n palauttama funkkari on reilusti nopeampi ku repeated_fold:in, mutta
# sen composen kasaaminen kestää ***1000x*** kauemmin esim. jos times=30
@inline repeated_compose(fn, times) = ∘(fill(fn, times)...)

# # foldl takes a fn (acc, x). (fn ∘ _left) is (acc,_) -> fn(acc)
# # this is basically just fn composed with itself `times` times (fn ∘ fn ∘ ... )
@inline repeated_fold(fn, times) = (input) -> (@inline; foldl((fn ∘ _left), 1:times; init=input))
@inline repeated_iter(fn, times) = inp -> (@inline; 1:times+1 |> Iterated(fn, inp) |> TakeLast(1) |> collect |> only)

@inline function repeated_for(fn, times)
  input -> begin
    @inline
    let fn = fn, times = times, out = fn(input)
      for _ in 1:(times-1)
        out = fn(out)
      end
      out
    end
  end
end

@inline _left(a, _) = a
@inline _left((a, _)) = a

const ArgHead = Val{:BindHead}
const ArgTail = Val{:BindTail}
const ArgPos = Union{ArgHead,ArgTail}

# ks @< ja @>
struct BoundCall{InitArgPos<:ArgPos,InitArg,F<:Base.Callable,KW} <: Function
  f::F
  arg::InitArg
  kw::KW

  _str::String

  function BoundCall{InitArgPos}(f::F, str_representation::String, x; kwargs...) where {InitArgPos,F}
    new{InitArgPos,_stable_typeof(x),F,_stable_typeof(kwargs)}(f, x, kwargs, str_representation)
  end

  function BoundCall{InitArgPos}(f::F, str_representation::String, x...; kwargs...) where {InitArgPos,F}
    new{InitArgPos,_stable_typeof(x),F,_stable_typeof(kwargs)}(f, x, kwargs, str_representation)
  end
end

@inline _stringify_argpos(::Type{ArgHead}) = ":ArgHead"
@inline _stringify_argpos(::Type{ArgTail}) = ":ArgTail"


Base.show(io::IO, b::BoundCall) = print(io, b._str)
Base.show(io::IO, ::MIME"text/plain", b::BoundCall{AP}) where {AP} = print(io,
  "BoundCall{",
  _stringify_argpos(AP), "}(",
  b._str, ")")

const BoundCallWTuple{InitArgPos} = BoundCall{InitArgPos,InitArg} where {InitArg<:Tuple}

const _EmptyKW = Base.Pairs{Symbol,Union{},Tuple{},NamedTuple{(),Tuple{}}}
const _emptyKW = pairs((;))

"Only call `merge` if both parameters are non-empty, otherwise just return the non-empty param"
@inline _merge_nonempty(d, other) = merge(d, other)
@inline _merge_nonempty(d, ::_EmptyKW) = d
@inline _merge_nonempty(::_EmptyKW, d) = d
@inline _merge_nonempty(::_EmptyKW, ::_EmptyKW) = _emptyKW

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

  let bfn = BoundCall{ArgHead}(fn, "fn", 1)
    @test bfn(2; d=4) == fn(1, 2; d=4)
    @test bfn(2; c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgHead}(fn, "fn", 1, 2)
    @test bfn(; d=4) == fn(1, 2; d=4)
    @test bfn(c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgHead}(fn, "fn")
    @test bfn(1, 2; d=4) == fn(1, 2; d=4)
    @test bfn(1, 2; c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgTail}(fn, "fn", 2)
    @test bfn(1; d=4) == fn(1, 2; d=4)
    @test bfn(1; c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgTail}(fn, "fn", 1, 2)
    @test bfn(d=4) == fn(1, 2; d=4)
    @test bfn(c=30, d=40) == fn(1, 2; c=30, d=40)
  end

  let bfn = BoundCall{ArgTail}(fn, "fn")
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


"""
    bound = @> fn(a,b)
    bound(c, d) == fn(a, b, c, d)

Bind a function call (or other callable, such as a type) so that arguments are bound starting from the first (left). The argument must be a function call with at least one argument, and zero or more keyword arguments.


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

export @>


"""
    @< fn(a)
    @< fn(a, b)
    @< fn(a; kw=1)

Bind a function call (or other callable, such as a type) so that arguments are bound starting from the tail (right). The argument must be a function call with at least one argument, 
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

export @<

function _stringify_arg(ex::Expr)
  # jos kw niin erillinen kw-stringify, muuten vaan string(ex)
  if ex.head === :kw
    string(ex.args[1]) * "=" * string(ex.args[2])
  else
    string(ex)
  end
end

_stringify_arg(x) = string(x)

_stringify_args(::Nothing) = ""
_stringify_args(args) = join(map(_stringify_arg, args), ",")
_stringify_kws(kws) = ";" * _stringify_args(kws)
_stringify_kws(::Nothing) = ""

_stringify_unbound_param(::Type{ArgHead}, ::Nothing) = "_xs..."
_stringify_unbound_param(::Type{ArgHead}, @nospecialize(args)) = ",_xs..."
_stringify_unbound_param(::Type{ArgTail}, ::Nothing) = "_xs..."
_stringify_unbound_param(::Type{ArgTail}, @nospecialize(args)) = "_xs...,"

_stringify_bound_call(T::Type{ArgHead}, fn, args, kws) = "_xs->" * string(fn) * "(" * _stringify_args(args) * _stringify_unbound_param(T, args) * _stringify_kws(kws) * ")"
_stringify_bound_call(T::Type{ArgTail}, fn, args, kws) = "_xs->" * string(fn) * "(" * _stringify_unbound_param(T, args) * _stringify_args(args) * _stringify_kws(kws) * ")"


function _bound(ex, argpos)
  function _string_sexpr(ex)
    io = IOBuffer()
    Meta.show_sexpr(io, ex)
    io |> take! |> String
  end
  @capture(ex, fn_(args__; kws__) | fn_(args__)) || error("Not used on a function call? Syntax: @> f(a, b; c = 1)")

  # @debug "bound" ex _string_sexpr(ex) args kws

  # if length(args) == 0 && length(kws) == 0
  #   error("Function call had no regular or keyword arguments. Syntax: @> f(a, b; c = 1)")
  # end

  # @debug fn args kws
  ex_str = _stringify_bound_call(Val{argpos}, fn, args, kws)
  fn = esc(fn)
  _args = !isnothing(args) ? map(esc, args) : []
  _kws = !isnothing(kws) ? map(esc, kws) : []
  # isnothing(kws) ? kws = Any[] : kws = map(esc, kws)

  quote
    Musica.BoundCall{Val{$(QuoteNode(argpos))}}($fn, $(ex_str), $(_args...), $(_kws...))
  end
end


@testitem "macros" begin
  fn(a, b; c, d=0) = (a - b) * (c + d)

  # pelkkä kw arg
  @test @<(fn(; c=5))(12, 2) == 50

  # pelkkä kw pitäis toimia samalla tavalla sekä @> että @<
  @test @>(fn(; c=5))(12, 2) == 50

  @test @>(fn(12))(2; c=5) == 50
  @test @>(fn(12, c=5))(2) == 50
  @test @>(fn(12; c=5))(2) == 50

  # testaa että hommat toimii myös konstruktoreiden kanssa. `Dada(n)`ssä `Dada`n tyyppi on `UnionAll` eikä
  # Function
  struct Dada{A,B,C}
    field::Int
  end

  Dada(v) = Dada{Int,Int,Int}(v)
  @test (@> Dada(5))() == Dada{Int,Int,Int}(5)

end

@inline _stable_typeof(x) = typeof(x)
@inline _stable_typeof(::Type{T}) where {T} = @isdefined(T) ? Type{T} : DataType

const indent::String = "  "

prettyprint_expr(e, level::Int=0) = prettyprint_expr(stdout, e, level)

function prettyprint_expr(io::IO, e, level::Int=0)

  lvl_indent = repeat(indent, level)
  args_indent = repeat(indent, level + 1)
  if isa(e, Expr)
    print(io, "\n",lvl_indent,"Expr(:")
    print(io, e.head, ", ")
    # if e.head in (:if, :ifelse, :block)
    #   print("\n", args_indent)
    # end
    first = true
    for arg in e.args
      if first
        first = false
      else
        print(io, ", ")
      end
      prettyprint_expr(io, arg, level + 1)
    end
    print(io, ")")
  elseif isa(e, Symbol)
    print(io, ":", e)
  elseif isa(e, QuoteNode)
    print(io, "QuoteNode(")
    prettyprint_expr(io, e.value)
    print(io, ")")
  else
    print(io, e)
  end
end