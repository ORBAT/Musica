using Transducers, StaticArrays, TestItems, Test

"""
    Row{NStates,Len,T,C<:AbstractArray}

A sized container type for 1-dimensional CA rows. `NStates` is the number of states per cell, eg. 2 for elementary cellular automata.

Is a subtype of `AbstractVector` and should implement the whole interface for it
"""
struct Row{NStates,Len,T,C<:AbstractArray} <: AbstractVector{T}
  coll::C

  function Row{NStates,Len,T,C}(c::C) where {NStates,Len,T,C<:Union{StaticVector{Len,T},SizedVector{Len,T}}}
    new(c)
  end

  function Row{NStates,Len,T,C}(c::C) where {NStates,Len,T,C<:AbstractArray}
    @assert length(c) == Len "Tried to construct a Row with Len type parameter $Len, but with a collection of length $(length(c))"
    new(c)
  end
end

Row{NS,L,T}(coll) where {NS,L,T} = Row{NS,L,T,typeof(coll)}(coll)
Row{NS,L}(coll) where {NS,L} = Row{NS,L,Base.eltype(coll)}(coll)
Row{NS}(coll::SV) where {NS,L,T,SV<:Union{StaticVector{L,T},SizedVector{L,T}}} = Row{NS,L,T,SV}(coll)

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

# conversions from one Row collection type to another (converts collection type from C to NC)
@inline Base.convert(::Type{Row{NS,L,T,NC}}, r::R) where {NS,L,T,NC,C,R<:Row{NS,L,T,C}} = Row{NS,L,T,NC}(convert(NC, r.coll))
# conversions from any AbstractArray to a Row
@inline Base.convert(::Type{Row{NS,L,T,C}}, c::C) where {NS,L,T,C<:AbstractArray} = Row{NS,L,T,C}(c)
@inline Base.convert(::Type{Row{NS,L,T}}, c::C) where {NS,L,T,C<:AbstractArray} = Row{NS,L,T,C}(c)

@forward Row.coll (Base.size, Base.getindex, Base.setindex!, Base.firstindex, Base.lastindex, Base.iterate,
  Base.length, Base.axes, eltype, Base.IteratorSize, Base.IteratorEltype)

struct DiscreteCA{NStates,Radius,RuleLen}
  rule::Int
  rule_lookup::SVector{RuleLen,Int}

  function DiscreteCA{NStates,Radius,RuleLen}(rule::Int) where {NStates,Radius,RuleLen}
    @assert 0 ≤ rule < (NStates^RuleLen) "rule number for $(NStates) states must be ≥ 0 and < $(NStates^RuleLen), was $(rule)"
    @assert RuleLen == NStates^(2 * Radius + 1) "RuleLen must be NStates^(2 * Radius + 1)"
    new(rule, rule_to_rule_lookup(rule, NStates, Radius))
  end
end

function DiscreteCA{NStates,Radius}(rule::Int) where {NStates,Radius}
  DiscreteCA{NStates,Radius,NStates^(2 * Radius + 1)}(rule)
end

function DiscreteCA{NStates}(rule::Int) where {NStates}
  DiscreteCA{NStates,1}(rule)
end

@testitem "CA initialization" begin
  @test_throws AssertionError DiscreteCA{2}(256)
  @test_throws AssertionError DiscreteCA{2}(-1)
  @test_throws AssertionError DiscreteCA{3}(3^27)
end

"""
* `NS` = `NStates`
* `RD` = `Radius`

**HOX HOX** kokeillu vähän kaikkea mutta tän return type jostain syystä vaan tahtoo olla `any` jos statea ei tyypitä
"""
function (dca::DiscreteCA{NS,RD,RuL})(state::State)::State where {NS,RD,RuL,L,State<:Row{NS,L}}
  # state wraps around at the ends
  ws = _wrap_state(state, RD)
  # run ws through xf, fold it into a container that's similar to `state` 
  xf = _transducer(dca)
  _collect_into!(xf, ws, similar(state))
end

"Feeds `foldable` into `xf` and collects the result into `init_state`. Mutates `init_state`"
_collect_into!(xf, foldable, init_state) =
  foldl(xf |> Enumerate(), foldable; init=init_state) do acc, (idx, a)
    # folds xf into init_state
    @inbounds acc[idx] = a
    acc
  end

"""
    _wrap_state(state, radius)

Make `state` wrap around at the ends by prepending the `radius` last elements and appending first elements.

Returns an [eduction](https://juliafolds.github.io/Transducers.jl/stable/reference/manual/#Transducers.eduction).
"""
_wrap_state(state, radius) = (@inbounds(@view(state[end-radius+1:end])), state, @inbounds(@view(state[1:radius]))) |> Cat()

neighborhood_size(::Type{DiscreteCA{NS,RD,RuL}}) where {NS,RD,RuL} = RD * 2 + 1

"""Return a transducer that applies the CA's rule.

- slices into windows (neighborhoods) of length neighborhood_size, 1 step at a time
- turns each neighborhood x into a number, uses that to index into the rule_lookup to get the result
"""
function _transducer(dca::T) where {T<:DiscreteCA}
  Consecutive(neighborhood_size(T), 1) |>
  Map(@© _lookup_rule(dca))
end

function _lookup_rule(dca::DiscreteCA{NS}, x) where {NS}
  dca.rule_lookup[undigits(x, NS)+1]
end

@testitem "evolution" begin
  using StaticArrays
  state = Row{2}(@SVector [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
  ca = DiscreteCA{2}(110)

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
undigits(d, base=2) = foldr((digit, acc) -> muladd(base, acc, digit), d, init=0)

"""
    Musica.rule_to_rule_lookup(rule::Int, nstates::Int = 2, radius::Int = 1)

Return a little-endian vector for the transition rule padded to the max rule length. 
Eg. for radius=1 nstates=2, index 1 is the result for 000, index 1 is for 001 etc.

```jldoctest
julia> x = Musica.rule_to_rule_lookup(30);

julia> show(x)
[0, 1, 1, 1, 1, 0, 0, 0]

```

See also [`undigits`](@ref)
"""
function rule_to_rule_lookup(rule::Int, nstates::Int=2, radius::Int=1)
  RuleLen = nstates^(2 * radius + 1)
  SVector{RuleLen,Int}(digits(Int, rule; base=nstates, pad=RuleLen))
end

@testitem "Rule number to rule lookup array" begin
  @test Musica.rule_to_rule_lookup(22, 3) == [[1, 1, 2]; zeros(Int, 27 - 3)]
end

function parser(::Type{DiscreteCA{2}};kw...)
  function p(bv)::Tuple{BitVector,DiscreteCA{2}}
    (bv |> Drop(8) |> collect, DiscreteCA{2}(undigits(bv |> Take(8) |> collect)))
  end
end

parser_bits_required(::Type{<:DiscreteCA{2}};kw...) = 8

"""
    Musica.num_as_ones(n, Val{N})

Return a `Row{2,N}` that contains `n` 1's. Little-endian, padded to length `N`

```jldoctest
julia> Musica.num_as_ones(6, Val{8})
8-element Row{2, 8, Int64, Vector{Int64}}:
 1
 1
 1
 1
 1
 1
 0
 0
```
"""
function num_as_ones(n::Integer, ::Type{Val{L}})::Row{2,L} where {L}
  @assert 0 ≤ n < BigInt(2)^L "n must be positive and smaller than 2^L ($(2^L)), was $n"
  Row{2,L}(digits(BigInt(2)^n - 1;base=2, pad=L))
end

function num_as_row(n::Integer, ::Type{Val{L}})::Row{2,L} where {L}
  Row{2,L}(digits(n;base=2,pad=L))
end

count_ones(r::Row{2})::Int = sum(filter(==(1), r))

@testitem "num_as_ones" begin
  @test_throws AssertionError Musica.num_as_ones(-1, Val{8})
  @test_throws AssertionError Musica.num_as_ones(256, Val{8})
end