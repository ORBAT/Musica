using Transducers, StaticArrays, TestItems, Test, Printf


const _SizedTypes{Len,T} = Union{StaticVector{Len,T},SizedVector{Len,T}}

"""
    Row{NStates,Len,T,C<:AbstractArray}

A sized container type for 1-dimensional CA rows. `NStates` is the number of states per cell, eg. 2 for elementary cellular automata.

Is a subtype of `AbstractVector` and should implement the whole interface for it
"""
struct Row{NStates,Len,T,C<:AbstractArray{T}} <: AbstractVector{T}
  coll::C

  # TODO FIXME: puljaa tää niin että T<:Union{Unsigned,Bool}

  function Row{NS,L,T,C}(c::C) where {NS,L,T,C<:AbstractArray{T}}
    new{NS,L,T,C}(c)
  end

end

export Row

function Row{2,L,T}(c::C) where {L,T<:Union{Signed,Unsigned},C<:AbstractArray{T}}
  # TODO FIXME: poista tää @warn-blokki sit ku tätä ei enimmäkseen tapahdu
  @warn begin
    t = join(_stacktrace(5), "\n")
    "Row{2,$L,$T,$C}: binary row constructor called with numeric T\n$t"
  end
  dest = similar(c, Bool)
  Row{2,L,Bool,typeof(dest)}(copyto!(dest, c))
end

function Row{NS,L,T}(c::C) where {NS,L,T,C}
  Row{NS,L,T,C}(c)
end

function Row{NS,L,T}(c::C) where {NS,L,T<:Signed,C}
  UT = unsigned(T)
  new_c = convert(AbstractArray{UT}, c)
  # TODO FIXME: poista tää @warn-blokki sit ku tätä ei enimmäkseen tapahdu
  @warn begin
    t = join(_stacktrace(5), "\n")
    "Row{$NS,$L,$T}(c): called with signed T $T, converting to $UT - $(typeof(new_c))\n$t"
  end
  Row{NS,L,UT,typeof(new_c)}(new_c)
end


@inline _condensed_str(coll::AbstractArray{Bool})::String = map(v -> v ? '1' : '0', coll) |> join
@inline _condensed_str(coll::AbstractArray{<:Integer})::String = map(v -> '1' + (v - 1), coll) |> join

function Base.show(io::IO, row::Row{NS,W,T}) where {NS,W,T<:Union{Bool, Unsigned}}
  print(io, "Row{", NS, ",", W, ",", T, "}(", _condensed_str(row.coll), ")")
end

function Base.show(io::IO, row::Row{NS,W,T}) where {NS,W,T}
  print(io, "Row{", NS, ",", W, ",", T, "}(", row.coll, ")")
end

function Base.show(io::IO, ::MIME"text/plain", row::Row{NS,W}) where {NS,W}
  show(io, row)
end

"""
Create a new `Row` from a `StaticVector` or a `SizedVector`.
"""
@inline function Row{NStates}(c::C) where {NStates,Len,T,C<:_SizedTypes{Len,T}}
  Row{NStates,Len,T}(c)
end

"""
Create a new `Row` from any `AbstractArray` `c`. Checks that `c`'s length is equal to `Len`
"""
@inline function Row{NStates,Len}(c::C) where {NStates,Len,T,C<:AbstractArray{T}}
  # @debug "Row generic constr"
  @assert length(c) == Len
  Row{NStates,Len,T}(c)
end


@inline Row{NS}(coll::AbstractArray) where {NS} = Row{NS,length(coll)}(coll)

@inline Base.IndexStyle(::Type{Row{NS,L,T,C}}) where {NS,L,T,C} = Base.IndexStyle(C)

@inline function Base.similar(r::Row{NStates,Len,T,C}) where {NStates,Len,T,C<:SizedVector}
  # TODO FIXME: tää riippuu SizedVectorin sisuskaluista. Jos tätä kikkailua ei tee, niin BitVectorin kanssa lopputulos on
  # SizedVector{Len, Bool, Vector{Bool}} eikä SizedVector{Len, Bool, BitVector}
  c = similar(r.coll.data)
  # @debug "Base.similar(Row) with SizedVector r.coll=$(typeof(r.coll)) c=$(typeof(c))"
  Row{NStates}(SizedVector{Len}(c))
end

@inline function Base.similar(r::Row{NStates,Len,T,C}) where {NStates,Len,T,C}
  c = similar(r.coll)
  # @debug "Base.similar(Row) r.coll=$(typeof(r.coll)) c=$(typeof(c))"
  Row{NStates,Len}(c)
end


"""
    Base.convert(::Type{Row{N,L,T,CS}}, x::Row{N,L,T,CM}) where {N,L,T,CS<:SVector{L,T},CM<:MVector{L,T}}
Convert a `Row` backed by a `MVector` to one backed by an `SVector`.
"""
@inline function Base.convert(::Type{Row{N,L,T,CS}}, x::Row{N,L,T,CM}) where {N,L,T,CS<:SVector{L,T},CM<:MVector{L,T}}
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
  bv = SizedVector{4}(ones(Bool, 4))
  # comparison with eg. Bool[]
  @test Row{2}(bv) == Bool[1, 1, 1, 1]

end

@forward Row.coll (Base.size, Base.getindex, Base.setindex!, Base.firstindex, Base.lastindex, Base.iterate,
  Base.length, Base.axes, eltype, Base.IteratorSize, Base.IteratorEltype)

struct DiscreteCA{NStates,Radius,RuleLen} <: Function
  rule::UInt
  rule_lookup::SVector{RuleLen,Int}

  function DiscreteCA{NStates,Radius,RuleLen}(rule) where {NStates,Radius,RuleLen}
    @assert 0 ≤ rule < (NStates^RuleLen)
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

HOX TODO: pitää ehkä tehdä tästä myös mutatoiva versio. CANeuron ja CANeuronStack tuottaa muuten aika paljon gorbagea
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

- TODO: tuki arvoille jotka on `> typemax(UInt64)`, koska muuten Row:n maksimipituus on 64


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
Row{2,8,Bool}(11111100)
```
"""
@inline function num_to_ones(n::Integer, ::Type{Val{L}})::Row{2,L} where {L}
  @assert 0 ≤ n < L "n must be positive and smaller than L ($L), was $n"
  Row{2,L}([ones(Bool, n); zeros(Bool, L - n)])
end

export num_to_ones

@inline function num_to_row(n::Integer, ::Type{Val{RowLen}})::Row{2,RowLen} where {RowLen}
  Row{2,RowLen}(digits(Bool, n; base=2, pad=RowLen))
end

@inline function num_to_row(n::Integer, ::Type{Val{Base}}, ::Type{Val{RowLen}})::Row{2,RowLen} where {RowLen,Base}
  Row{Base,RowLen}(digits(n; base=Base, pad=RowLen))
end

export num_to_row

@inline (Base.count_ones(r::T)::Int) where {T<:Union{AbstractArray{Bool},Row}} = sum(filter(==(1), r))

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

function _stacktrace(top_n, remove_first=5)
  trace = stacktrace()[remove_first:end]
  trace[1:min(length(trace), top_n)]
end
