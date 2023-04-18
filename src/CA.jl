using Transducers, StaticArrays, TestItems, Test

struct DiscreteCA{NStates,Radius,RuleLen}
  rule::Int
  rule_lookup::SVector{RuleLen,Int}
  nstates::Int
  radius::Int

  function DiscreteCA{NStates,Radius,RuleLen}(rule::Int) where {NStates,Radius,RuleLen}
    @assert 0 ≤ rule < (NStates^RuleLen) "rule number for $(NStates) states must be ≥ 0 and < $(NStates^RuleLen), was $(rule)"
    @assert RuleLen == NStates^(2 * Radius + 1) "RuleLen must be NStates^(2 * Radius + 1)"
    new(rule, rule_to_rule_lookup(rule, Val{NStates}(), Val{Radius}()), NStates, Radius)
  end
end

function DiscreteCA{NStates,Radius}(rule::Int) where {NStates,Radius}
  DiscreteCA{NStates,Radius,NStates^(2 * Radius + 1)}(rule)
end

@testitem "CA initialization" begin
  @test_throws AssertionError DiscreteCA{2,1}(256)
  @test_throws AssertionError DiscreteCA{2,1}(-1)
  @test_throws AssertionError DiscreteCA{3,1}(3^27)
end

"""
* `NS` = `NStates`
* `RD` = `Radius`

**HOX HOX** kokeillu vähän kaikkea mutta tän return type jostain syystä vaan tahtoo olla `any` jos statea ei tyypitä
"""
function (dca::DiscreteCA{NS,RD,RuL})(state::State)::State where {NS,RD,RuL,State}
  new_state = similar(state)
  # state wraps around at the ends
  wrapped_state = wrapped_state_eduction(state, RD)
  # run wrapped_state through xf, fold it into new_state 
  xf = transducer(dca)
  _collect_into!(xf, wrapped_state, new_state)
end

"Feeds `foldable` into `xf` and collects the result into `init_state`. Mutates `init_state`"
@inline _collect_into!(xf, foldable, init_state) =
  foldl(xf |> Enumerate(), foldable; init=init_state) do acc, (idx, a)
    @inline
    # folds xf into init_state
    acc[idx] = a
    acc
  end

"""Make `state` wrap around at the ends by prepending the `radius` last elements and appending first elements.

Returns an [eduction](https://juliafolds.github.io/Transducers.jl/stable/reference/manual/#Transducers.eduction).
"""
@inline wrapped_state_eduction(state, radius) = (@view(state[end-radius+1:end]), state, @view(state[1:radius])) |> Cat()

@inline neighborhood_size(::Type{DiscreteCA{NS,RD,RuL}}) where {NS,RD,RuL} = RD * 2 + 1

"""Returns a transducer that applies the CA's rule.

- slices into windows (neighborhoods) of length neighborhood_size, 1 step at a time
- turns each neighborhood x into a number, uses that to index into the rule_lookup to get the result
"""
@inline function transducer(dca::T) where {NS,RD,RuL,T<:DiscreteCA{NS,RD,RuL}}
  Consecutive(neighborhood_size(T), 1) |>
  Map(x -> @inline dca.rule_lookup[undigits(x, NS)+1])
end

@testitem "evolution" begin
  using StaticArrays
  state = @SVector [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ca = DiscreteCA{2,1}(110)

  @test ca(state) == [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  @inferred(ca(state))
end

"""
    undigits(d, base=2)

Treat d as a little-endian vector of digits in `base` and return the base-10 representation.

```jldoctest
julia> Musica.undigits([0, 1, 1, 1, 1, 0, 0, 0])
30

julia> Musica.undigits(Musica.rule_to_rule_lookup(22, 3), 3)
22
```
"""
@inline undigits(d, base=2) = foldr((digit, acc) -> muladd(base, acc, digit), d, init=0)

"""
    rule_to_rule_lookup(rule::Int, nstates::Int = 2, radius::Int = 1)

Return a little-endian vector for the transition rule padded to the max rule length. 
Eg. for radius=1 nstates=2, index 0 is the result for 000, index 1 is for 001 etc.

```jldoctest
julia> x = Musica.rule_to_rule_lookup(30);

julia> show(x)
[0, 1, 1, 1, 1, 0, 0, 0]

```

See also [`undigits`](@ref)
"""
@inline function rule_to_rule_lookup(rule::Int, nstates::Int=2, radius::Int=1)
  rule_to_rule_lookup(rule, Val(nstates), Val(radius))
end

@inline function rule_to_rule_lookup(rule::Int, ::Val{NStates}, ::Val{Radius}) where {NStates,Radius}
  RuleLen = NStates^(2 * Radius + 1)
  SVector{RuleLen,Int}(digits(Int, rule, base=NStates, pad=RuleLen))
end

@testitem "Rule number to rule lookup array" begin
  @test Musica.rule_to_rule_lookup(22, 3) == [[1, 1, 2]; zeros(Int, 27 - 3)]
end

###################### TODO

"""
    Row{NStates,Len,T,C<:AbstractArray}

A sized container type for 1-dimensional CA rows. `NStates` is the number of states per cell, eg. 2 for elementary cellular automata.

Is a subtype of `AbstractVector` and should implement the whole interface for it
"""
struct Row{NStates,Len,T,C<:AbstractArray} <: AbstractVector{T}
  coll::C

  function Row{NStates,Len,T,C}(c::C) where {NStates,Len,T,C<:AbstractArray}
    @assert length(c) == Len "Tried to construct a Row with Len type parameter $Len, but with a collection of length $(length(c))"
    new(c)
  end
end

@inline Row{NStates,Len,T}(coll) where {NStates,Len,T} = Row{NStates,Len,T,typeof(coll)}(coll)
@inline Row{NStates,Len}(coll) where {NStates,Len} = Row{NStates,Len,Base.eltype(coll)}(coll)
@inline Row{NStates}(coll::SV) where {NStates,Len,T,SV<:StaticVector{Len,T}} = Row{NStates,Len,T,SV}(coll)

@inline Base.IndexStyle(::Type{Row{NS,L,T,C}}) where {NS,L,T,C} = Base.IndexStyle(C)

@inline function Base.similar(r::Row{NStates,Len,T,C}) where {NStates,Len,T,C}
  c = similar(r.coll)
  Row{NStates,Len,T,typeof(c)}(c)
end

@inline function Base.similar(r::Row{NStates,Len,T,C}, dims::Int...) where {NStates,Len,T,C}
  @assert foldl(*, dims) == Len "dims gives a length of $(foldl(*,dims)) but Len was $Len"
  c = similar(r.coll, dims...)
  Row{NStates,Len,T,typeof(c)}(c)
end
# Base.similar(r::Row{NStates,Len,T,C}, dims::Dims) where {NStates,Len,T,C} = Base.similar(r, dims...)

# conversions from one Row collection type to another (converts collection type from C to NC)
@inline Base.convert(::Type{Row{NS,L,T,NC}}, r::R) where {NS,L,T,NC,C,R<:Row{NS,L,T,C}} = Row{NS,L,T,NC}(convert(NC, r.coll))

# conversions from any AbstractArray to a Row
@inline  Base.convert(::Type{Row{NS,L,T,C}}, c::C) where {NS,L,T,C<:AbstractArray} = Row{NS,L,T,C}(c)
@inline  Base.convert(::Type{Row{NS,L,T}}, c::C) where {NS,L,T,C<:AbstractArray} = Row{NS,L,T,C}(c)

@forward Row.coll (Base.size, Base.getindex, Base.setindex!, Base.firstindex, Base.lastindex, Base.iterate,
  Base.length, Base.axes, eltype, Base.IteratorSize, Base.IteratorEltype)