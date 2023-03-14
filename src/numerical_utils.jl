"""
undigits(digits_, base=Val(2))

Treat `digits_` as a little-endian vector of digits in `base` and return the base-10 representation.

- TODO: tuki arvoille jotka on `> typemax(UInt64)`, koska muuten Row:n maksimipituus on 64

```jldoctest
julia> undigits([0, 1, 1, 1, 1, 0, 0, 0])
0x000000000000001e

julia> undigits(CA.rule_to_rule_lookup(0x16, 3), Val(3))
0x0000000000000016

julia> undigits([])
0x0000000000000000
```
"""
Base.@constprop :aggressive @propagate_inbounds undigits(digits_, base::Integer) = undigits(digits_, Val(base))
@propagate_inbounds function undigits(digits_, baseval::Val{base}=Val(2)) where {base}
  if length(digits_) == 0
    return UInt(0)
  end
  @boundscheck @assert _fits_in_64_bits(digits_, baseval) "d does not fit in 64 bits and undigits only returns UInt64 for now"

  (s, b) = (UInt(0), UInt(base))
  mult = UInt(1)
  for val in digits_
    s += val * mult
    mult *= b
  end
  s
end

export undigits

"""
_typemax_digits(type, base)::SVector{N,UInt64}
"""
## TODO FIXME: kääntäminen vetää usein jökkiin jos käyttää @memoize:a.
Base.@constprop :aggressive @inline function _typemax_digits(type, _eltype, ::Val{base}, ::Val{NDigits}) where {base,NDigits}
  SVector{NDigits,_eltype}(digits(typemax(type); base=base))
end

Base.@constprop :aggressive @inline _typemax_digits(type, _eltype, b::Val{base}) where {base} = _typemax_digits(type, _eltype, b, Val(_ndigits_of_typemax(type, b))) #= @memoize ThreadSafeDict  =#

Base.@assume_effects :foldable _ndigits_of_typemax(t, ::Val{base}) where {base} = ndigits(typemax(t); base=base)

"""
_fits_in_64_bits([1,2,0,1], base=Val{3})
tarkistaa että `number` mahtuu 64 bittiin. Olettaa, että `number` on little endian
"""
@inline function _fits_in_64_bits(digits_, b::Val{base}=Val(2)) where {base}
  # TODO: tiputa numberista alkunollat pois
  maxval = _typemax_digits(UInt64, eltype(digits_), b)
  let num_len = length(digits_), maxval_len = length(maxval)
    if num_len > maxval_len
      return false
    elseif num_len < maxval_len
      return true
    end
  end

  for i in eachindex(digits_)
    @inbounds if digits_[i] > maxval[i]
      return false
    end
  end
  return true
end

@inline _bits_needed(num_digits, base) = ceil(Int, num_digits * log2(base))

#=
undigits(d; base = 10) = foldr((a, b) -> muladd(base, b, a), d, init=0)
=#

@testitem "undigits" begin
  @test undigits([0, 1, 1, 1, 1, 0, 0, 0]) == 0x000000000000001e
  @test_throws AssertionError undigits(ones(Bool, 65))
  @test_throws AssertionError undigits(ones(Int, 41), 3)
  @test undigits(digits(typemax(UInt64); base=3), 3) == typemax(UInt64)
  let max_plus_1 = let max = digits(typemax(UInt64); base=3)
      max[1] = 1
      max
    end
    @test_throws AssertionError undigits(max_plus_1, 3)
  end
end