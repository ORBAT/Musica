using Transducers, StaticArrays, TestItems, Test, Printf


const _SizedTypes{Len, T} = Union{StaticVector{Len,T},SizedVector{Len,T}}

"""
    Row{NStates,Len,T,C<:AbstractArray}

A sized container type for 1-dimensional CA rows. `NStates` is the number of states per cell, eg. 2 for elementary cellular automata.

Is a subtype of `AbstractVector` and should implement the whole interface for it
"""
struct Row{NStates,Len,T,C<:AbstractArray} <: AbstractVector{T}
  coll::C

  #TODO: ei ehkä tarvii näin monta inner constructoria? Järkeistä vähän

  function Row{NS,L,T,C}(c::C) where {NS,L,T,C<:AbstractArray}
    @assert length(c) == L "Tried to construct a Row with Len type parameter $Len, but with a collection of length $(length(c))"
    new{NS,L,T,C}(c)
  end

  function Row{NS,L,T,C}(c::C) where {NS,L,T,C<:_SizedTypes{L, T}}
    new{NS,L,T,C}(c)
  end


  """
  Create a new `Row` from a `StaticVector` or a `SizedVector`.
  """
  function Row{NStates}(c::C) where {NStates,Len,T,C<:_SizedTypes{Len, T}}
    # @debug "Row{NStates} SizedVector"
    new{NStates,Len,T,C}(c)
  end

  function Row{2}(c::C) where {Len,T,C<:_SizedTypes{Len, T}}
    # @debug "Row{2} SizedVector{Len,T}" typeof(c)
    new_c = SizedVector{Len}(BitVector(c))
    new{2,Len,Bool,SizedVector{Len,Bool,BitVector}}(new_c)
  end

  function Row{2}(c::C) where {Len,C<:SizedVector{Len,Bool,BitVector}}
    # @debug "Row{2} SizedVector{Len,Bool,BitVector}" typeof(c)
    new{2,Len,Bool,C}(c)
  end

  function Row{2, Len}(c::C) where {Len,C<:SizedVector{Len,Bool,BitVector}}
    # @debug "Row{2} SizedVector{Len,Bool,BitVector}" typeof(c)
    new{2,Len,Bool,C}(c)
  end

  function Row{2,Len}(c::C) where {Len,C<:BitVector}
    # @debug "Row{2} BitVector"
    @assert length(c) == Len "Tried to construct a Row with Len type parameter $Len, but with a collection of length $(length(c))"
    new{2,Len,Bool,SizedVector{Len,Bool,BitVector}}(SizedVector{Len}(c))
  end

  function Row{2,Len}(c::C) where {Len,C<:AbstractArray}
    # @debug "Row{2} AbstractArray $C"
    @assert length(c) == Len "Tried to construct a Row with Len type parameter $Len, but with a collection of length $(length(c))"
    new{2,Len,Bool,SizedVector{Len,Bool,BitVector}}(SizedVector{Len}(BitVector(c)))
  end

  """
  Create a new `Row` from any `AbstractArray` `c`. Checks that `c`'s length is equal to `Len`
  """
  function Row{NStates,Len}(c::C) where {NStates,Len,T,C<:AbstractArray{T}}
    # @debug "Row generic constr"
    @assert length(c) == Len "Tried to construct a Row with Len type parameter $Len, but with a collection of length $(length(c))"
    new{NStates,Len,T,C}(c)
  end
end

export Row

function Base.show(io::IO, row::Row{NS,W}) where {NS,W}
  print(io, "Row{", NS, ",", W, "}(", row.coll, ")")
end

function Base.show(io::IO, ::MIME"text/plain", row::Row{NS,W}) where {NS,W}
  print(io, "Row{", NS, ",", W, "}(", row.coll, ")")
end

@inline Row{NS}(coll) where {NS} = Row{NS, length(coll)}(coll)

#Row{NS,L,T}(coll) where {NS,L,T} = Row{NS,L,T,typeof(coll)}(coll)
#Row{NS,L}(coll) where {NS,L} = Row{NS,L,Base.eltype(coll)}(coll)
#Row{NS}(coll::SV) where {NS,L,T,SV<:Union{StaticVector{L,T},SizedVector{L,T}}} = Row{NS,L}(coll)

@inline Base.IndexStyle(::Type{Row{NS,L,T,C}}) where {NS,L,T,C} = Base.IndexStyle(C)

@inline function Base.similar(r::Row{NStates,Len,T,C}) where {NStates,Len,T,C<:SizedVector}
  # TODO FIXME: tää riippuu SizedVectorin sisuskaluista. Jos tätä kikkailua ei tee, niin BitVectorin kanssa lopputulos on
  # SizedVector{Len, Bool, Vector{Bool}} eikä SizedVector{Len, Bool, BitVector}
  c = similar(r.coll.data)
  # @debug "Base.similar(Row) with SizedVector r.coll=$(typeof(r.coll)) c=$(typeof(c))"
  Row{NStates,Len}(SizedVector{Len}(c))
end

@inline function Base.similar(r::Row{NStates,Len,T,C}) where {NStates,Len,T,C}
  c = similar(r.coll)
  # @debug "Base.similar(Row) r.coll=$(typeof(r.coll)) c=$(typeof(c))"
  Row{NStates,Len}(c)
end


"""
Convert a `Row` backed by a `MVector` to one backed by an `SVector`.
"""
@inline function Base.convert(::Type{Row{N,L,T,CS}}, x::Row{N,L,T,CM}) where {N,L,T,CS<:SVector{L, T}, CM<:MVector{L, T}}
  Row{N,L,T,CS}(SVector{L}(x))
end

#QUE: tarviiks?
#= @inline function Base.similar(r::Row{NStates,Len,T,C}, dims::Int...) where {NStates,Len,T,C}
  @assert foldl(*, dims) == Len "dims gives a length of $(foldl(*,dims)) but Len was $Len"
  c = similar(r.coll, dims...)
  Row{NStates,Len}(c)
end
 =#
 
@testitem "Row" begin
  using StaticArrays
  bv = SizedVector{4}(BitVector(ones(Bool, 4)))
  # comparison with eg. Bool[]
  @test Row{2}(bv) == Bool[1, 1, 1, 1]

end

@forward Row.coll (Base.size, Base.getindex, Base.setindex!, Base.firstindex, Base.lastindex, Base.iterate,
  Base.length, Base.axes, eltype, Base.IteratorSize, Base.IteratorEltype)

struct DiscreteCA{NStates,Radius,RuleLen} <: Function
  rule::UInt
  rule_lookup::SVector{RuleLen,Int}

  function DiscreteCA{NStates,Radius,RuleLen}(rule) where {NStates,Radius,RuleLen}
    @assert 0 ≤ rule < (NStates^RuleLen) "rule number for $(NStates) states must be ≥ 0 and < $(NStates^RuleLen), was $(rule)"
    _r = convert(UInt, rule)
    @assert RuleLen == NStates^(2 * Radius + 1) "RuleLen must be NStates^(2 * Radius + 1)"
    new(rule, rule_to_rule_lookup(_r, NStates, Radius))
  end
end

export DiscreteCA

@inline function Base.hash(a::DiscreteCA{N,R,RL}, h::UInt) where {N,R,RL}
  hash(:DiscreteCA, h) |> @©(hash(N)) |> @©(hash(R)) |> @©(hash(a.rule))
end

@inline function Base.:(==)(a::DiscreteCA{N1,R1}, b::DiscreteCA{N2,R2}) where {N1,R1,N2,R2}
  isequal(N1, N2) && isequal(R1, R2) && isequal(a.rule, b.rule)
end

function Base.show(io::IO, ca::DiscreteCA{2,1})
  @printf(io, "DiscreteCA(ECA %3i)", ca.rule)
end

function DiscreteCA{NStates,Radius}(rule) where {NStates,Radius}
  DiscreteCA{NStates,Radius,NStates^(2 * Radius + 1)}(rule)
end

function DiscreteCA{NStates}(rule) where {NStates}
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
@inline function (dca::DiscreteCA{NS,RD,RuL})(state::State)::State where {NS,RD,RuL,L,State<:Row{NS,L}}
  # state wraps around at the ends
  ws = _wrap_state(state, RD)
  # run ws through xf, fold it into a container that's similar to `state` 
  xf = _transducer(dca)
  _ss = similar(state)
  # @info "(dca)(state)" typeof(state) state typeof(_ss) _ss
  _collect_into!(xf, ws, _ss)
end

"Feeds `foldable` into `xf` and collects the result into `collection`. Mutates `collection`"
_collect_into!(xf, foldable, collection) =
  foldl(xf |> Enumerate(), foldable; init=collection) do acc, (idx, a)
    # folds xf into collection
    @inbounds acc[idx] = a
    acc
  end

"""
    _wrap_state(state, radius)

Make `state` wrap around at the ends by prepending the `radius` last elements and appending first elements.

Returns an [eduction](https://juliafolds.github.io/Transducers.jl/stable/reference/manual/#Transducers.eduction).
"""
@inline _wrap_state(state, radius) = (@inbounds(@view(state[end-radius+1:end])), state, @inbounds(@view(state[1:radius]))) |> Cat()

#QUE QUE: vaikka tää versio on ittessään vitusti nopeampi ku toi versio missä on Cat(), niin jotenkin ite CA on silti reilusti hitaampi jos tätä käyttää. MIKSI HÄ MITÄ VITTUA
@inline function _wrap_state2(state, radius)
  slen = length(state)
  idxs = [slen-radius+1:slen; 1:slen; 1:radius]
  @inbounds @views state[idxs]
end

@inline _neighborhood_size(::Type{<:DiscreteCA{NS,RD}}) where {NS,RD} = RD * 2 + 1

"""Return a transducer that applies the CA's rule.

- slices into windows (neighborhoods) of length neighborhood_size, 1 step at a time
- turns each neighborhood x into a number, uses that to index into the rule_lookup to get the result
"""
@inline function _transducer(dca::T) where {T<:DiscreteCA}
  Consecutive(_neighborhood_size(T), 1) |>
  Map(@© _lookup_rule(dca))
end

# HUOM: käyttäytyy ihan vitun huonosti jos x ei oo indeksi rule_lookup:issa, koska @inbounds
@inline function _lookup_rule(dca::DiscreteCA{NS}, x) where {NS}
  @inbounds dca.rule_lookup[undigits(x, NS)+1]
end

@testitem "evolution" begin
  using StaticArrays
  state = Row{2}(BitVector([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
  ca = DiscreteCA{2}(110)

  @test ca(state) == [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  @inferred(ca(state))

  state_b3 = Row{3}(@SVector [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
  ca_b3 = DiscreteCA{3}(110)
  @inferred(ca_b3(state_b3))
end

"""
    undigits(d, base=2)

Treat d as a little-endian vector of digits in `base` and return the base-10 representation.

- TODO: tuki arvoille jotka on `> typemax(UInt64)`


```jldoctest
julia> undigits([0, 1, 1, 1, 1, 0, 0, 0])
0x000000000000001e

julia> undigits(Musica.rule_to_rule_lookup(22, 3), 3)
0x0000000000000016

julia> undigits([])
0x0000000000000000
```
"""
undigits(d, base=2) = foldr((digit, acc) -> muladd(base, acc, digit), d, init=UInt(0))

export undigits

"""
    Musica.rule_to_rule_lookup(rule::UInt, nstates::Int = 2, radius::Int = 1)

Return a little-endian vector for the transition rule padded to the max rule length. 
Eg. for radius=1 nstates=2, index 1 is the result for 000, index 1 is for 001 etc.

```jldoctest
julia> x = Musica.rule_to_rule_lookup(30);

julia> show(x)
[0, 1, 1, 1, 1, 0, 0, 0]

```

See also [`undigits`](@ref)
"""
@inline function rule_to_rule_lookup(rule::Integer, nstates::Int=2, radius::Int=1)
  RuleLen = nstates^(2 * radius + 1)
  SVector{RuleLen,Int}(digits(Int, rule; base=nstates, pad=RuleLen))
end

@testitem "Rule number to rule lookup array" begin
  @test Musica.rule_to_rule_lookup(22, 3) == [[1, 1, 2]; zeros(Int, 27 - 3)]
end

@inline function parser(::Type{DiscreteCA{2}}; kw...)
  Parser() do bits
    (bits |> Drop(8) |> collect, DiscreteCA{2}(undigits(bits |> Take(8) |> collect)))
  end
end

@testitem "parser" begin
  @test digits(110; base=2) |> Musica.parser(DiscreteCA{2}) == (Bool[], DiscreteCA{2}(110))
end

@inline parser_bits_required(::Type{<:DiscreteCA{2}}; kw...) = 8

"""
    num_to_ones(n, Val{N})

Return a `Row{2,N}` that contains `n` 1's. Little-endian, padded to length `N`

```jldoctest
julia> num_to_ones(6, Val{8})
Row{2,8}(Bool[1, 1, 1, 1, 1, 1, 0, 0])
```
"""
@inline function num_to_ones(n::Integer, ::Type{Val{L}})::Row{2,L} where {L}
  @assert 0 ≤ n < L "n must be positive and smaller than L ($L), was $n"
  Row{2,L}([ones(Bool, n); zeros(Bool, L - n)])
end

export num_to_ones

@inline function num_to_row(n::Integer, _row_len::Type{Val{L}})::Row{2,L} where {L}
  Row{2,L}(digits(n; base=2, pad=L))
end

@inline function num_to_row(n::Integer, _base::Type{Val{Base}}, _row_len::Type{Val{L}})::Row{2,L} where {L,Base}
  Row{Base,L}(digits(n; base=Base, pad=L))
end

export num_to_row

@inline count_ones(r::Row)::Int = sum(filter(==(1), r))

export count_ones

@testitem "num_to_ones" begin
  @test_throws AssertionError num_to_ones(-1, Val{8})
  @test_throws AssertionError num_to_ones(256, Val{8})
end

@inline num_from_gray(n) = UInt(Integer(reinterpret(Gray64, n)))

export num_from_gray

@inline row_to_number(r::Row{2}) = r |> undigits
@inline row_to_number(r::Row{N}) where {N} = r |> @£(undigits(N))

export row_to_number

"""
Interpret a `Row` as being a Gray-coded integer
"""
@inline row_from_gray(r::Row{2}) = r |> undigits |> num_from_gray

export row_from_gray

@inline num_to_gray(x) = (x ⊻ (x >> 1))

export num_to_gray

@inline num_to_gray_row(x, w::Type{Val{width}}) where {width} = x |> num_to_gray |> @£ num_to_row(w)
@inline num_to_gray_row(x, width::Int) = num_to_gray_row(x, Val{width})
@inline num_to_gray_row(x) = num_to_gray_row(x, Val{16})

export num_to_gray_row

@testitem "gray coding" begin
  row_width = Val{5}
  @test row_from_gray(num_to_row(5, row_width)) == 6
  @test row_from_gray(num_to_row(10, row_width)) == 12
  @test row_from_gray(num_to_row(1, row_width)) == 1
  @test num_to_gray_row(12, row_width) == num_to_row(10, row_width)
end