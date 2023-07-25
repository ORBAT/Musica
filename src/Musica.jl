"""
Musica is a genetic programming framework.

  - bioinspired genome
  - cellular automata instead of a "traditional" VM like PushGP
"""
module Musica

function __enable_debug(xs...=("Main", "Musica")...)
  prev = get(ENV, "JULIA_DEBUG", "")
  ENV["JULIA_DEBUG"] = join(xs, ",")
  prev
end

function __enable_debug(within::Function, xs...=("Main", "Musica")...)
  old = __enable_debug(xs...)
  within()
  __enable_debug(old)
end

using Base: @propagate_inbounds
using Static, StaticArrays, Try, TryExperimental

## HOX: "backport" julian masterissa olevista muutoksista, nopeampaa viewien iterointia
# ks https://github.com/JuliaLang/julia/pull/48720
# HUOM: aiheuttaa invalidaatioita kääntäessä
if VERSION < v"1.9.3"
  function Base.checkindex(::Type{Bool}, inds::Base.IdentityUnitRange, i::Real)
    Base.checkindex(Bool, inds.indices, i)
  end
  function Base.checkindex(::Type{Bool}, inds::Base.OneTo{T}, i::T) where {T<:Base.BitInteger}
    unsigned(i) ≤ unsigned(last(inds))
  end
end

# ATTN: brazen type piracy to implement https://github.com/JuliaLang/julia/pull/34293, to make folding heterogenous iterators a _lot_ faster.
# This is bad and I should feel bad.
#
# Doesn't do the "manual union splitting" with `if v isa T` because it didn't seem to have any effect on performance for either short or long arrays.
#
### Perf 
## unmodified:
# let xs=1:1000 |> Interpose(missing) |> collect
#   @btime sum(x for x in $xs if x !== missing)
#   end
## 2.616 μs (0 allocations: 0 bytes)
#
## Modified: 
##     759.698 ns (0 allocations: 0 bytes)
#
# TODO: will this be needed after Parser is refactored? Mmmmmmaybe not?
function Base._foldl_impl(op::OP, init, itr) where {OP}
  y = iterate(itr)
  y === nothing && return init
  v = op(init, y[1])
  return _foldl_impl(op, v, itr, y[2], static(10))
end

@inline function _foldl_impl(
  op::OP,
  acc::T,
  itr,
  state,
  @nospecialize(counter::StaticInt)
) where {OP,T}
  while true
    y = iterate(itr, state)
    y === nothing && return acc
    x, state = y
    result = op(acc, x)
    counter === static(0) || result isa T ||
      return _foldl_impl(op, result, itr, state, counter - static(1))
    acc = result
  end
end

include("macros.jl")
include("function_utils.jl")
include("collection_utils.jl")
include("numerical_utils.jl")
include("parser.jl")
include("ca.jl")
include("Neuron.jl")
include("optimize.jl")

include("./GA/GA.jl")
include("RefCap.jl")

function workload()
  s = CA.Elementary(110)(_new_state(Val(16)))
  @show s

  let inp = Vector{Bool}[[1, 0, 1, 0], [1, 0, 1, 1], [1, 0, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]],
    want2 = [0, 1, 0, 0, 1, 1] |> undigits,
    want3 = [0, 1, 0, 0, 1, 1, 0, 0, 1] |> undigits

    @show Parser.execute(Parser.Varints{2}(), inp) ==
          Parser.Ok(Parser.S(want2, [[1, 0, 0, 1], [0, 1, 1, 1], [1, 1, 1, 1]]))

    @show Parser.execute(Parser.Varints{4}(), inp) ==
          Parser.Ok(Parser.S(want3, [[0, 1, 1, 1], [1, 1, 1, 1]]))

    @show Parser.execute(Parser.Varints{4}(), Vector{Bool}[]) |> Parser.iserr
  end

  let inp = Vector{Bool}[[0, 1, 1, 1], [1, 0, 1, 0]], want = UInt(0b111)
    @show Parser.execute(Parser.Varints{2}(), inp) ==
          Parser.Ok(Parser.S(want, [Bool[1, 0, 1, 0]]))
  end
end

end
