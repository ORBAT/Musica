using Transducers, StaticArrays, TestItems, Printf, GrayCode, AutoHashEquals

"""
    Row{NStates,Len} <: AbstractVector{T}

A sized container type for 1-dimensional CA rows.
`NStates` is the number of states per cell, eg. 2 for elementary cellular automata. `Len` is the length of the row. `T` is the eltype.

NOTE that `Row` is little-endian, so the first element of the "parent vector" it's constructed with is the least significant. This mirrors [`digits`](@ref) and [`Musica.undigits`](@ref).

If you index with a `SVector` or a static range `static(n):static(m)`, `Row` returns a `Row` with the correct length. Otherwise returns a `Vector{T}`

```jldoctest; setup = :(using StaticArrays, Static)
julia> 33 |> @>(digits(; base=2, pad=8)) |> Row{2,8} |> undigits |> Int
33

julia> r = Row{2}(@SVector Bool[1, 0, 0, 1, 0]);

julia> r[@SVector [2, 4]] # NOTE: little-endian so result is 10 and not 01
Row{2,2}(0b10)

julia> r[static(2):static(4)] # NOTE: little-endian so result is 100 and not 001
Row{2,3}(0b100)
```
"""
struct Row{NStates,Len,T,C<:AbstractVector{T}} <: AbstractVector{T}
  coll::C

  function Row{NStates,Len}(coll::C) where {NStates,Len,T,C<:AbstractVector{T}}
    @assert length(coll) == Len
    _require_1_based_idx(coll)
    new{NStates,Len,T,C}(coll)
  end

  # StaticArrays tarvii tätä että StaticArrays.similar_type toimii, ja sitä taas vaatii noi staattiset ei-skalaari-indeksit r[static(1):static(5)] jne
  function Row{N,L,T,C}(coll::NTuple{L,T}) where {N,L,T,C<:StaticVector{L,T}}
    _require_1_based_idx(coll)
    new{N,L,T,C}(coll)
  end

  function Row{N,L,T,C}(coll::C) where {N,L,T,C<:StaticVector{L,T}}
    _require_1_based_idx(coll)
    new{N,L,T,C}(coll)
  end

  function Row{N,L,T,C}(coll::C) where {N,L,T,C<:AbstractVector{T}}
    _require_1_based_idx(coll)
    @assert length(coll) == L
    new{N,L,T,C}(coll)
  end
end

_require_1_based_idx(coll) = @assert axes(coll) == (coll |> length |> Base.OneTo,)

Row{NStates}(coll::C) where {NStates,Len,T,C<:StaticVector{Len,T}} = Row{NStates,Len,T,C}(coll)

function Row{N,L}(coll::NTuple{L,T}) where {N,L,T}
  sv = SVector(coll)
  Row{N,L,T,sv |> typeof}(sv)
end

function Row{N}(coll::NTuple{L,T}) where {N,L,T}
  sv = SVector(coll)
  Row{N,L,T,sv |> typeof}(sv)
end

Row{NStates,Len}(coll::C) where {NStates,Len,T,C<:StaticVector{Len,T}} = Row{NStates,Len,T,C}(coll)

Row{2}(coll::C) where {Len,C<:StaticVector{Len,Bool}} = Row{2,Len,Bool,C}(coll)

Row{2,Len}(coll::C) where {Len,C<:StaticVector{Len,Bool}} = Row{2,Len,Bool,C}(coll)

function Row{2,Len}(coll::C) where {Len,C<:AbstractVector{Bool}}
  @assert length(coll) == Len
  Row{2,Len,Bool,C}(coll)
end

export Row

# HUOM: tän avulla StaticArrays.Length toimii
@inline StaticArrays.Size(::Type{<:Row{NStates,Len}}) where {NStates,Len} = Size(Len)

Base.:(==)(r1::Row{N,L}, r2::Row{N′,L′}) where {N,L,N′,L′} =
  N == N′ && L == L′ && r1.coll == r2.coll

# @inline _condensed_str(coll::AbstractArray{Bool})::String = map(v -> v ? '1' : '0', coll) |> join
@inline _condensed_str(e) = map(v -> '0' + v, e) |> reverse |> join

function Base.show(io::IO, row::Row{2,L}) where {L}
  print(io, "Row{2,", L, "}(0b", row.coll |> _condensed_str, ")")
end

function Base.show(io::IO, row::Row{NS,L,T}) where {NS,L,T<:Union{Bool,Unsigned}}
  print(io, "Row{", NS, ",", L, ",", T, "}(", row.coll |> @>(string(; base=NS)), ")")
end

Base.show(io::IO, ::MIME"text/plain", row::Row{NS,W}) where {NS,W} = show(io, row)

@inline Base.IndexStyle(@nospecialize(_::Type{Row{NS,L,T,C}})) where {NS,L,T,C} =
  Base.IndexStyle(C)
@inline Base.IteratorSize(@nospecialize(_::Type{Row{NS,L,T,C}})) where {NS,L,T,C} =
  Base.IteratorSize(C)
@inline Base.IteratorEltype(@nospecialize(_::Type{Row{NS,L,T,C}})) where {NS,L,T,C} =
  Base.IteratorEltype(C)

# KYSYM: miks tää taas olikaan tarpeellinen?
@inline function Base.similar(r::Row{NStates,Len,T,C}) where {NStates,Len,T,C<:SizedVector}
  c = similar(parent(r.coll))
  Row{NStates}(SizedVector{Len}(c))
end

@inline function Base.similar(r::Row{NStates,Len}) where {NStates,Len}
  c = similar(r.coll)
  Row{NStates,Len}(c)
end

@inline Core.Tuple(r::Row{NStates,Len,T}) where {NStates,Len,T} = NTuple{Len,T}(r.coll)

#=

They must define the following methods:
 - `Tuple()`, returning the data in a flat Tuple.

- `similar_type(::Type{MyStaticArray}, ::Type{NewElType}, ::Size{NewSize})`, returning a
  type (or type constructor) that accepts a flat tuple of data.

For mutable containers you may also need to define the following:

 - `setindex!` for a single element (linear indexing).
 - `similar(::Type{MyStaticArray}, ::Type{NewElType}, ::Size{NewSize})`.
 - In some cases, a zero-parameter constructor, `MyStaticArray{...}()` for unintialized data
   is assumed to exist.

  =#

function Base.similar(
  r::Row{NStates,Len},
  dims::Tuple{SR},
) where {NStates,Len,SR<:Static.SUnitRange}
  l = length(dims[1])
  Row{NStates,l}(similar(r.coll, l))
end

function Base.similar(
  r::Row{NStates,Len},
  ::Type{NewEltype},
  ::Size{NewSize},
) where {NStates,Len,NewEltype,NewSize}
  l = prod(NewSize)
  Row{NStates,l}(similar(r.coll, l))
end

function StaticArrays.similar_type(
  ::Type{<:Row{N,L,OT,C}},
  ::Type{T},
  ::Size{S},
) where {N,L,OT,C,T,S}
  Row{N,S[1],T,similar_type(C, T, Size(S))}
end

@inline Base.parent(r::Row) = r.coll

parenttype(::Type{Row{N,L,T,CS}}) where {N,L,T,CS} = CS
parenttype(r::Row)                                 = r |> typeof |> parenttype

@inline Base.convert(::Type{Row{N,L,T,CS}}, x::Row{N,L,T,CS}) where {N,L,T,CS} = x
@inline Base.convert(::Type{Row{N,L,T,CS}}, x::Row{N,L,T}) where {N,L,T,CS} =
  Row{N,L,T,CS}(convert(CS, x |> parent))

"""
a::Row ⊻ b::Row
XOR
"""
@propagate_inbounds function Base.:⊻(a::Row{2,L}, b::Row{2,L}) where {L}
  collect_into!(similar(a), a.coll .⊻ b.coll)
end

@propagate_inbounds function Base.:⊻(a::Row{N,L,Ta}, b::Row{N,L,Tb}) where {N,L,Ta,Tb}
  T = promote_type(Ta, Tb)
  Row{N}(@.(T(mod(a.coll + b.coll, N))))
end

@testitem "XOR" begin
  using StaticArrays
  let r1 = Row{2}(@SVector [true, false]), r2 = Row{2}(@SVector [false, true])
    @test r1 ⊻ r2 == Row{2}(@SVector [true, true])
  end

  let r1 = Row{3}(@SVector [0, 1, 2]), r2 = r1
    @test r1 ⊻ r2 == Row{3}(@SVector [0, 2, 1])
  end
end

@inline to_immutable(r::Row{N,L,T,C}) where {N,L,T,C<:SVector} = r
@inline to_immutable(r::Row{N,L}) where {N,L}                  = r |> parent |> SVector{L} |> Row{N}
"""
    to_mutable(r)

Create a mutable **copy** of `r`.
"""
@inline to_mutable(r::Row) = collect_into!(similar(r), r)

@forward Row.coll (
  Base.size,
  Base.setindex!,
  Base.firstindex,
  Base.lastindex,
  Base.iterate,
  Base.length,
  Base.axes,
  Base.eltype,
)

# HOX: jos tän määritteli forwardilla, niin tuli ambiguityä Accessorsin kanssa ¯\_(ツ)_/¯
@propagate_inbounds function Base.getindex(x::Row, i::Int)
  @boundscheck checkbounds(x, i)
  x.coll[i]
end

@testitem "Row" begin
  using StaticArrays, Static
  bv = SizedVector{4}(ones(Bool, 4))
  # comparison with eg. Bool[]
  @test Row{2}(bv) == Bool[1, 1, 1, 1]

  @test Row{2}(bv)[static(2):static(3)] == Row{2}(SizedVector{2}(bv[2:3]))
end

function _stacktrace(top_n, remove_first=4)
  trace = stacktrace()[remove_first+1:end]
  trace[1:min(length(trace), top_n)]
end

"""
    CA.num_to_ones(n, Val{N})

Return a `Row{2,N}` that contains `n` 1's. Little-endian, padded to length `N`

```jldoctest
julia> CA.num_to_ones(6, Val(8))
Row{2,8}(0b00111111)
```
"""
@inline function num_to_ones(n::Integer, ::Val{L})::Row{2,L} where {L}
  @assert 0 ≤ n < L
  Row{2,L}([ones(Bool, n); zeros(Bool, L - n)])
end

export num_to_ones

@inline num_to_row(T::Type, n::Integer, ::Val{L}) where {L} = num_to_row(T, n, Val(2), Val{L}())

@inline num_to_row(n::Integer, ::Val{L}) where {L} = num_to_row(SVector{L}, n, Val(L))

@inline function num_to_row(
  T::Type,
  n::Integer,
  ::Val{_Base},
  ::Val{RowLen},
) where {RowLen,_Base}
  Row{_Base,RowLen}(T(digits(n; base=_Base, pad=RowLen)))
end

@inline function num_to_row(
  n::Integer,
  ::Val{Base},
  ::Val{RowLen},
) where {RowLen,Base}
  num_to_row(BitVector, n, Val(2), Val(RowLen))
end

export num_to_row

@inline (Base.count_ones(r::T)::Int) where {T<:Row} = filter(==(1), r) |> sum

@testitem "num_to_ones" begin
  @test_throws AssertionError CA.num_to_ones(-1, Val(8))
  @test_throws AssertionError CA.num_to_ones(256, Val(8))
end

Base.@assume_effects :foldable @inline num_from_gray(n) = UInt(Integer(reinterpret(Gray64, n)))

export num_from_gray

@inline row_to_number(r::Row{2})           = r |> undigits
# TODO[low-prio]
@inline row_to_number(r::Row{N}) where {N} = r |> @< undigits(Val(N))

export row_to_number

"""
Interpret a `Row` as being a Gray-coded integer
"""
@inline row_from_gray(r::Row{2}) = r |> undigits |> num_from_gray

export row_from_gray

@inline num_to_gray(x) = (x ⊻ (x >> 1))

export num_to_gray

@inline num_to_gray_row(x, w::Val{width}) where {width} = x |> num_to_gray |> @< num_to_row(w)
@inline num_to_gray_row(x, width::Int)                  = num_to_gray_row(x, Val(width))
@inline num_to_gray_row(x)                              = num_to_gray_row(x, Val{16})

export num_to_gray_row

@testitem "gray coding" begin
  row_width = Val(5)
  @test CA.row_from_gray(CA.num_to_row(5, row_width)) == 6
  @test CA.row_from_gray(CA.num_to_row(10, row_width)) == 12
  @test CA.row_from_gray(CA.num_to_row(1, row_width)) == 1
  @test CA.num_to_gray_row(12, row_width) == CA.num_to_row(10, row_width)
end

"""
    CA.new_state(Val(RowWidth))

Creates a new `Row{2}`
"""
function new_state(::Val{L}) where {L}
  let bla = zeros(Bool, L)
    bla[1] = true
    Row{2}(SVector{L}(bla))
  end
end

function new_state(::Type{T}, ::Val{L}) where {T,L}
  let bla = zeros(Bool, L)
    bla[1] = true
    Row{2,L}(T(bla))
  end
end
