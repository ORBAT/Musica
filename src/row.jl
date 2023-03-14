using Transducers, StaticArrays, TestItems, Printf, GrayCode
using ..Musica: SizedType

"""
    Row{NStates,Len,T,C<:AbstractArray}

A sized container type for 1-dimensional CA rows. 
`NStates` is the number of states per cell, eg. 2 for elementary cellular automata. `Len` is the length of the row. `T` is the type of the cells, ie. the eltype.

Is a subtype of `AbstractVector` and should implement the whole interface for it
"""
struct Row{NStates,Len,T,C<:AbstractArray{T}} <: AbstractVector{T}
  # TODO FIXME: coll vois aina olla <:SizedType{Len,T}
  coll::C
end

export Row

# HUOM: tän avulla StaticArrays.Length toimii
@inline StaticArrays.Size(::Type{<:Row{NStates,Len}}) where {NStates,Len} = Size(Len)

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


"""
Create a new `Row` from a `StaticVector` or a `SizedVector`.
"""
function Row{NStates}(c::C) where {NStates,Len,T,C<:SizedType{Len,T}}
  Row{NStates,Len,T}(c)
end

"""
Create a new `Row` from any `AbstractArray` `c`. Checks that `c`'s length is equal to `Len`
"""
function Row{NStates,Len}(c::C) where {NStates,Len,T,C<:AbstractArray{T}}
  # @debug "Row generic constr"
  @assert length(c) == Len
  Row{NStates,Len,T}(c)
end

@inline _condensed_str(coll::AbstractArray{Bool})::String = map(v -> v ? '1' : '0', coll) |> join
@inline _condensed_str(coll::AbstractArray{<:Integer})::String = map(v -> '0' + v, coll) |> join

function Base.show(io::IO, row::Row{NS,W,T}) where {NS,W,T<:Union{Bool,Unsigned}}
  print(io, "Row{NS=", NS, ",W=", W, ",T=", T, "}(", _condensed_str(row.coll), ")")
end

function Base.show(io::IO, row::Row{NS,W,T}) where {NS,W,T}
  print(io, "Row{NS=", NS, ",W=", W, ",T=", T, "}(", row.coll, ")")
end

function Base.show(io::IO, ::MIME"text/plain", row::Row{NS,W}) where {NS,W}
  show(io, row)
end

@inline Base.IndexStyle(@nospecialize(_::Type{Row{NS,L,T,C}})) where {NS,L,T,C} = Base.IndexStyle(C)
@inline Base.IteratorSize(@nospecialize(_::Type{Row{NS,L,T,C}})) where {NS,L,T,C} = Base.IteratorSize(C)
@inline Base.IteratorEltype(@nospecialize(_::Type{Row{NS,L,T,C}})) where {NS,L,T,C} = Base.IteratorEltype(C)

@inline function Base.similar(r::Row{NStates,Len,T,C}) where {NStates,Len,T,C<:SizedVector}
  c = similar(parent(r.coll))
  Row{NStates}(SizedVector{Len}(c))
end

@inline function Base.similar(r::Row{NStates,Len,T,C}) where {NStates,Len,T,C}
  c = similar(r.coll)
  Row{NStates,Len}(c)
end

@inline Base.parent(r::Row) = r.coll

@inline Base.convert(::Type{Row{N,L,T,CS}}, x::Row{N,L,T,CS}) where {N,L,T,CS} = x
@inline Base.convert(::Type{Row{N,L,T,CS}}, x::Row{N,L,T}) where {N,L,T,CS} = Row{N,L,T,CS}(convert(CS, x |> parent))

# """
#     convert(Row{2,32,Bool,SVector{32,Bool}}, Row{2,32}(@MVector [1,1]))
# Convert a `Row` backed by a `MVector` to one backed by an `SVector`.
# """
# @inline function Base.convert(::Type{Row{N,L,T,CS}}, x::Row{N,L,T,CM}) where {N,L,T,CS<:SVector{L,T},CM<:MVector{L,T}}
#   Row{N,L,T,CS}(SVector{L}(x))
# end

# @inline function Base.convert(::Type{Row{N,L,T,CM}}, x::Row{N,L,T,CS}) where {N,L,T,CS<:SVector{L,T},CM<:MVector{L,T}}
#   Row{N,L,T,CM}(MVector{L}(x))
# end

##HOX: tän avulla esim. _zero_pad_array toimis Row:n kanssa, mutta tulee runtime dispatch koska toi vitun dim ei oo staattinen value adskjdsakjhdaskjh
## _ja_ C<:SizedVector muuttuu Vector:iksi
# @inline function Base.similar(r::Row{NStates,Len,T,C}, dim::Int) where {NStates,Len,T,C}
#   # @assert foldl(*, dims) == Len "dims gives a length of $(foldl(*,dims)) but Len was $Len"
#   c = similar(r.coll, dim)
#   Row{NStates,dim,T,typeof(c)}(c)
# end

"""
  a::Row ⊻ b::Row
XOR
"""
@propagate_inbounds function Base.:⊻(a::Row{2,L,Bool}, b::Row{2,L,Bool}) where {L}
  Row{2,L,Bool}(a.coll .⊻ b.coll)
end

@propagate_inbounds function Base.:⊻(a::Row{N,L,Ta}, b::Row{N,L,Tb}) where {N,L,Ta,Tb}
  T = promote_type(Ta, Tb)
  Row{N,L,T}(@.(T(mod(a.coll + b.coll, N))))
end

@inline to_immutable(r::Row{N,L,T,C}) where {N,L,T,C<:SVector} = r
@inline to_immutable(r::Row{N,L}) where {N,L} = r |> parent |> SVector{L} |> Row{N}
"""
    to_mutable(r)
Create a mutable copy of `r`.
"""
@inline to_mutable(r::Row{N,L}) where {N,L} = r |> parent |> MVector{L} |> Row{N}


## HOX: tää allaoleva on himpun hitaampi (tai ihan parhaimmillaankin breakeven) vrt nykynen _wrap_state:lla toimiva, wtf.

@forward Row.coll (Base.size, Base.getindex, Base.setindex!, Base.firstindex, Base.lastindex, Base.iterate,
  Base.length, Base.axes, Base.eltype)

@testitem "Row" begin
  using StaticArrays
  bv = SizedVector{4}(ones(Bool, 4))
  # comparison with eg. Bool[]
  @test Row{2}(bv) == Bool[1, 1, 1, 1]
end

function _stacktrace(top_n, remove_first=4)
  trace = stacktrace()[remove_first+1:end]
  trace[1:min(length(trace), top_n)]
end


"""
    CA.num_to_ones(n, Val{N})

Return a `Row{2,N}` that contains `n` 1's. Little-endia≤n, padded to length `N`

```jldoctest
julia> CA.num_to_ones(6, Val(8))
Row{NS=2,W=8,T=Bool}(11111100)
```
"""
@inline function num_to_ones(n::Integer, ::Val{L})::Row{2,L} where {L}
  @assert 0 ≤ n < L
  Row{2,L}([ones(Bool, n); zeros(Bool, L - n)])
end

export num_to_ones

@inline function num_to_row(n::Integer, ::Val{RowLen})::Row{2,RowLen} where {RowLen}
  Row{2,RowLen}(digits(Bool, n; base=2, pad=RowLen))
end

@inline function num_to_row(n::Integer, ::Val{Base}, ::Val{RowLen})::Row{2,RowLen} where {RowLen,Base}
  Row{Base,RowLen}(digits(n; base=Base, pad=RowLen))
end

export num_to_row

@inline (Base.count_ones(r::T)::Int) where {T<:Row} = filter(==(1), r) |> sum

@testitem "num_to_ones" begin
  @test_throws AssertionError CA.num_to_ones(-1, Val(8))
  @test_throws AssertionError CA.num_to_ones(256, Val(8))
end

Base.@assume_effects :foldable @inline num_from_gray(n) = UInt(Integer(reinterpret(Gray64, n)))

export num_from_gray

@inline row_to_number(r::Row{2}) = r |> undigits
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
@inline num_to_gray_row(x, width::Int) = num_to_gray_row(x, Val(width))
@inline num_to_gray_row(x) = num_to_gray_row(x, Val{16})

export num_to_gray_row

@testitem "gray coding" begin
  row_width = Val(5)
  @test CA.row_from_gray(CA.num_to_row(5, row_width)) == 6
  @test CA.row_from_gray(CA.num_to_row(10, row_width)) == 12
  @test CA.row_from_gray(CA.num_to_row(1, row_width)) == 1
  @test CA.num_to_gray_row(12, row_width) == CA.num_to_row(10, row_width)
end

