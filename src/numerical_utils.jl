using Random, Distributions
"""
undigits(digits_, Val(2)) # Val(2) is the base

Treat `digits_` as a little-endian vector of digits_ in `base` and return the base-10 representation.

NOTE: if you know that `digits_` would fit in 64 bits, call with `@inbounds`: `@inbounds undigits(digits_)` to skip the check, which can potentially make `digits_` slower by multiple factors

  - TODO: tuki arvoille jotka on `> typemax(UInt64)`, koska muuten Row:n maksimipituus on 64

```jldoctest
julia> undigits([0, 1, 1, 1, 1, 0, 0, 0])
0x000000000000001e

julia> undigits(CA.rule_to_rule_lookup(0x16, 3), Val(3))
0x0000000000000016
```
"""
Base.@constprop :aggressive @propagate_inbounds undigits(digits_, base::Integer) =
  undigits(digits_, Val(base))

@propagate_inbounds function undigits(digits_, baseval::Val{base}=Val(2)) where {base}
  @boundscheck if length(digits_) == 0
    throw(ArgumentError("digits is empty"))
  end
  @boundscheck @assert fits_in_T(UInt, digits_, baseval) "digits does not fit in 64 bits and undigits only returns UInt64 for now"

  (s, b) = (UInt(0), UInt(base))
  mult = UInt(1)
  for val in digits_
    s += val * mult
    mult *= b
  end
  s
end

export undigits

# TODO: figure out how terrible of an idea :foldable is here
Base.@assume_effects :foldable @inline function _typemax_digits(
  type,
  _eltype,
  ::Val{base},
  ::Val{NDigits},
) where {base,NDigits}
  SVector{NDigits,_eltype}(digits!(zeros(_eltype, NDigits), typemax(type); base=base))
  # SVector{NDigits,_eltype}(digits(typemax(type); base=base))
end

Base.@assume_effects :foldable Base.@constprop :aggressive @inline _typemax_digits(
  type,
  _eltype,
  b::Val{base},
) where {base} = _typemax_digits(type, _eltype, b, Val(_ndigits_of_typemax(type, b)))

@inline Base.@assume_effects :foldable _ndigits_of_typemax(t, ::Val{base}) where {base} =
  ndigits(typemax(t); base=base)

# -1 if digits_ has fewer nonzero digits than maxval_len, 1 if it has more and 0 if it has the same amount
function _cmp_length_to_max(digits_, maxval_len)
  # find the first non-zero significant digit (starting from the "big" end, hence findlast)
  let firstnonzero::Int = some(findlast(!iszero, digits_), 0)
    if firstnonzero == 0 # no non-zero digits at all, so definitely fits
      return -1
    end

    # first nonzero significant digit is past the maximum length, so definitely doesn't fit
    if firstnonzero > maxval_len
      return 1
    else
      let num_len = length(digits_), nonzero_len = num_len - (num_len - firstnonzero)
        return cmp(nonzero_len, maxval_len)
      end
    end
  end
  error("unreachable")
end

"""
_fits_in_T(Int, [1,2,0,1] Val{3})
Tarkistaa, että `b`-kantainen lista lukuja `digits_` mahtuu numeroksi muutettuna tyyppiin `T``
"""
@inline function fits_in_T(T, digits_, b::Val{base}=Val(2)) where {base}
  maxval_len = _ndigits_of_typemax(T, b)

  let _cmp = _cmp_length_to_max(digits_, maxval_len)
    if _cmp != 0
      # true if digits_ has fewer nonzero digits than maxval_len
      return _cmp == -1
    end
  end

  # ATTN: using UInt8 as the element type allows this to get constant folded at least for base-3
  maxval = _typemax_digits(T, UInt8, b, Val(maxval_len))

  # NOTE: digits_ and maxval are the same length so we can just go with `eachindex(digits_)` and use `@inbounds`
  let _cmp::Int64
    # yeah yeah it's naughty to loop like this and not use eg. reverse(eachindex(digits_)), but this is much faster and it Should Be Fine™ for now
    for i in static(maxval_len):static(-1):static(1)
      _cmp = @inbounds(cmp(digits_[i], maxval[i]))
      if _cmp != 0
        return _cmp == -1
      end
    end
  end
  return true
end

@testitem "undigits" begin
  _to_num(s; base=3) = s |>
                       @<(split("")) |>
                       @>(map(@>(parse(UInt)))) |>
                       @<(undigits(Val(3)))

  @test Musica.fits_in_T(UInt64, digits(typemax(UInt64); base=3), Val(3))
  @test Musica.fits_in_T(UInt64, digits(UInt128, typemax(UInt64) + UInt128(1); base=3), Val(3)) ==
        false

  # fits_in_T:ssä oli idioottimainen bugi; iteroi big endian -järjestyksessä…

  # base-3 uint max =         "02211201201202102011210102122122002221111"
  @test let base3_shouldfit = "20211201201202102011210102122122002221111" |> _to_num
    base3_shouldfit == 0xfffffffffffffffb
  end

  @test undigits([0, 1, 1, 1, 1, 0, 0, 0]) == 0x000000000000001e
  @test_throws AssertionError undigits(ones(Bool, 65))
  @test ones(Int, 41) |>
        @<(undigits(Val(3))) |>
        @>(digits(UInt128; base=3)) ==
        ones(Int, 41)

  @test undigits(digits(typemax(UInt64); base=3), 3) == typemax(UInt64)

  let max_plus_1 = digits(UInt128, typemax(UInt64) + UInt128(1); base=3)
    @test_throws AssertionError undigits(max_plus_1, 3)
  end
end

"""
    randn_prob(prob, n=1, range=0.5; [rng=Random.default_rng()])

Generate random numbers that fall within +/-`range` of 0 with probability `prob`.

Defaults to a range of 0.5, so it generates random numbers that round to 0 with probability `prob`
"""
randn_prob(prob, n=1, range=0.5; rng=Random.default_rng()) =
  let sd = quantile(Normal(), (1 + prob) / 2)
    randn(rng, n) * (range / sd)
  end
