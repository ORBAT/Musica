struct Elementary{NStates,Radius,RuleLen} <: Abstract
  rule::UInt
  # FIXME: SVector not great for larger `RuleLen`s
  rule_lookup::SVector{RuleLen,UInt8}

  """
  Elementary(110)
  Constructor for "classic" elementary CAs, where `NStates=2` and `Radius=1`
  """
  @propagate_inbounds function Elementary(rule)
    @boundscheck @assert 0 ≤ rule < 256
    new{2,1,0}(rule, SVector{0}())
  end

  @propagate_inbounds function Elementary{NStates,Radius}(rule) where {NStates,Radius}
    rule_len = NStates^(2 * Radius + 1)
    @boundscheck @assert 0 ≤ rule < (NStates^rule_len)
    _r = UInt8(rule)
    new{NStates,Radius,rule_len}(_r, rule_to_rule_lookup(_r, NStates, Radius))
  end
end

"""
    ECA

Type alias for the "classic" elementary CAs with 2 states, radius 1.
"""
const ECA = Elementary{2,1,0}

@propagate_inbounds Elementary{2,1}(rule)                     = Elementary(rule)
@propagate_inbounds Elementary{NStates}(rule) where {NStates} = Elementary{NStates,1}(rule)

@inline DomainType(::Type{Elementary{N}}) where {N} = Discrete(N)

@inline function Base.hash(a::Elementary{N,R,RL}, h::UInt) where {N,R,RL}
  hash(:Elementary, h) |> @>(hash(N)) |> @>(hash(R)) |> @>(hash(RL)) |> @>(hash(a.rule))
end

@inline function Base.:(==)(a::Elementary{N1,R1}, b::Elementary{N2,R2}) where {N1,R1,N2,R2}
  isequal(N1, N2) && isequal(R1, R2) && isequal(a.rule, b.rule)
end

function Base.show(io::IO, ca::Elementary{NS,Rd}) where {NS,Rd}
  @printf(io, "ECA{NStates=%i,Radius=%i}(%3i)", NS, Rd, ca.rule)
end

function Base.show(io::IO, ca::Elementary{2,1})
  @printf(io, "ECA(%3i)", ca.rule)
end

Base.show(io::IO, ::MIME"text/plain", ca::Elementary) = show(io, ca)

@testitem "CA initialization" begin
  @test_throws AssertionError CA.Elementary(256)
  @test_throws AssertionError CA.Elementary(-1)
  @test_throws AssertionError CA.Elementary{3}(3^27)
end

DomainType(::Type{<:Elementary{NS}}) where {NS} = Discrete{NS}

"""
Returns a Transducers.jl eduction that iterates over `r` like the edges wrapped around with a radius of `R`
"""
@inline _toroidal_educt(::Val{R}, r::Row{N,L}) where {R,N,L} =
  SOneTo{L + 2R}() |>
  Map(idx -> @inbounds r[Musica._to_toroidal_idx(idx, R, L)]) |>
  Consecutive(Val(neighborhood_size(R)), Val(1))

@propagate_inbounds apply_ca!(ca::Elementary{NS,Rad}, row::Row{NS}) where {NS,Rad} =
  collect_into!(row, _applied_eduction(ca, row))

@propagate_inbounds _applied_eduction(ca::Elementary{NS,Rad}, row::Row{NS}) where {NS,Rad} =
  _toroidal_educt(Val(Rad), row) |> Map(@>(apply_rule(ca)))

@propagate_inbounds apply_rule(dca::Elementary{NS}, x) where {NS} =
  dca.rule_lookup[undigits(x, Val(NS))+1] # +1 because array indexing starts at 1

@inline function apply_rule(dca::Elementary{2,1}, (right, center, left))
  # HUOM: bitit käänteisessä järjestyksessä eli `right` vasemmalla ja `left` oikealla, koska sekä `digits` että `undigits` on little endian
  # FIXME: right,center,left in correct order. Bit twiddling has to be changed for that
  N = (left << 2) | (center << 1) | right
  ((dca.rule >> N) & 1)
end

#= TODO apply_rule for nstates=2, radius>1
function apply_rule(rule::UInt128, bits)
    assert(1 ≤ length(bits) ≤ 7, "Invalid neighborhood size")
    N = 0
    for i in length(bits):-1:1
        N = (N << 1) | bits[i]
    end
    return (rule >> N) & 1
end
=#

neighborhood_size(::Type{<:Elementary{NS,R}}) where {NS,R} = neighborhood_size(R)

"""
    CA.rule_to_rule_lookup(rule, nstates = 2, radius = 1)

Return a little-endian vector for the transition rule padded to the max rule length.
Eg. for radius=1 nstates=2, index 1 is the result for 000, index 1 is for 001 etc.

```jldoctest
julia> x = CA.rule_to_rule_lookup(30);

julia> show(x)
UInt8[0x00, 0x01, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00]
```

See also [`undigits`](@ref)
"""
Base.@constprop :aggressive @inline function rule_to_rule_lookup(rule, nstates=2, radius=1)
  RuleLen = nstates^(2 * radius + 1)
  SVector{RuleLen,UInt8}(digits(UInt8, rule; base=nstates, pad=RuleLen))
end

@testitem "Rule number to rule lookup array" begin
  # 22 is 211 in base-3, but rule_to_rule_lookup outputs a little-endian array so we need to reverse it and add zero padding
  @test CA.rule_to_rule_lookup(22, 3) == [[1, 1, 2]; zeros(Int, 27 - 3)]
end

@testitem "evolution" begin
  using StaticArrays
  state = Row{2,11}(BitVector(Bool[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
  ca = CA.Elementary(110)

  @test ca(state) == [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  @inferred(ca(state))

  state_b3 = Row{3}(@SVector[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
  ca_b3 = CA.Elementary{3}(110)
  @inferred(ca_b3(state_b3))
end