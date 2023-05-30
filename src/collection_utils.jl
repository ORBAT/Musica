using Transducers
using Transducers: start, inner, @next, wrap, unwrap, complete

@inline maybe_collect(x) = x
@inline maybe_collect(x::T) where {T<:Transducers.Eduction} = x |> collect

"""
    LiftToArray()

A transducer that lifts its input into an array.

```jldoctest; setup=:(using Transducers)
# using Transducers
julia> [1,0,1] |> Map(x -> 2x) |> Musica.LiftToArray() |> Map(x -> Musica.undigits(x,3)) |> collect
1-element Vector{UInt64}:
 0x0000000000000014
```
"""
struct LiftToArray <: Transducer end

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


#NOTE: https://github.com/JuliaData/SplitApplyCombine.jl/blob/8534d12b7c6f78c85dcad9b22f7c6f619d62a9f4/src/only.jl
@inline function only(iter)
  i = iterate(iter)
  if i === nothing
      throw(ArgumentError("Collection must have exactly one element (input is empty)"))
  end
  (out, state) = i
  if iterate(iter, state) === nothing
      return out
  else
      throw(ArgumentError("Collection must have exactly one element (input contains more than one element)"))
  end
end

@inline function only(::Tuple{})
  throw(ArgumentError("Collection must have exactly one element (input is empty)"))
end
@inline function only(t::Tuple{Any})
  return t[1]
end
@inline function only(::NTuple{N,Any}) where N
  throw(ArgumentError("Collection must have exactly one element (input has $N elements)"))
end