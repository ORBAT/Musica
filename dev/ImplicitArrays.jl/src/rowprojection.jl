"""
    RowProjectionVector{T} <: AbstractArray{T, 1}

Implicit vector projecting a sequence of rows of a given vector with elements of type `T`.

# Constructors
    RowProjectionVector(base, rows)
    RowProjectionVector(base, rows...)
    RowProjectionVector{T}(base, rows)

Create a new row-projected vector from the given `base` vector and a list or sequence of
`rows` corresponding to it. Rows can be used multiple times and in any order.

# Examples

```jldoctest; setup = :(using ImplicitArrays)
julia> v = [10, 20, 30, 40, 50];

julia> RowProjectionVector(v, [1, 3, 5])
3-element RowProjectionVector{Int64}:
 10
 30
 50

julia> RowProjectionVector(v, 2, 3, 2)
3-element RowProjectionVector{Int64}:
 20
 30
 20
```

!!! note
    Changing an element through `RowProjectionVector` actually changes the element in the
    underlying array. The changes are still reflected in the `RowProjectionVector`. Thus,
    caution is advised when changing elements of rows that are contained multiple times
    in the projection, in order to avoid unwanted side effects.
"""
struct RowProjectionVector{T} <: AbstractArray{T, 1}
    "Base vector from which the projection is created"
    base::AbstractArray{T, 1}
    "Rows used for the projection"
    rows::Vector{Int}

    function RowProjectionVector{T}(
        base::AbstractArray{T, 1},
        rows::Vector{Int}
    ) where T
        @boundscheck _checkrowbounds(base, rows)
        new(base, rows)
    end
end

RowProjectionVector(
    base::AbstractArray{T, 1},
    rows::Vector{Int}
) where T = RowProjectionVector{T}(base, rows)

RowProjectionVector(
    base::AbstractArray{T, 1},
    rows::Vararg{Int, N}
) where {T, N} = RowProjectionVector(base, collect(rows))

@inline Base.size(
    M::RowProjectionVector{T}
) where T = (length(M.rows),)

@inline Base.getindex(
    M::RowProjectionVector{T},
    i::Int
) where T = Base.getindex(M.base, M.rows[i])

@inline Base.setindex!(
    M::RowProjectionVector{T},
    v::Any,
    i::Int
) where T = Base.setindex!(M.base, v, M.rows[i])


"""
    RowProjectionMatrix{T} <: AbstractArray{T, 2}

Implicit matrix projecting a sequence of rows of a given matrix with elements of type `T`.

# Constructors
    RowProjectionMatrix(base, rows)
    RowProjectionMatrix(base, rows...)
    RowProjectionMatrix{T}(base, rows)

Create a new row-projected matrix from the given `base` matrix and a list or sequence of
`rows` corresponding to it. Rows can be used multiple times and in any order.

# Examples

```jldoctest; setup = :(using ImplicitArrays)
julia> M = [10 20 30; 40 50 60; 70 80 90];

julia> RowProjectionMatrix(M, [1, 3])
2×3 RowProjectionMatrix{Int64}:
 10  20  30
 70  80  90

julia> RowProjectionMatrix(M, 2, 3, 2)
3×3 RowProjectionMatrix{Int64}:
 40  50  60
 70  80  90
 40  50  60
```

!!! note
    Changing an element through `RowProjectionMatrix` actually changes the element in the
    underlying array. The changes are still reflected in the `RowProjectionMatrix`. Thus,
    caution is advised when changing elements of rows that are contained multiple times
    in the projection, in order to avoid unwanted side effects.
"""
struct RowProjectionMatrix{T} <: AbstractArray{T, 2}
    "Base matrix from which the projection is created"
    base::AbstractArray{T, 2}
    "Rows used for the projection"
    rows::Vector{Int}

    function RowProjectionMatrix{T}(
        base::AbstractArray{T, 2},
        rows::Vector{Int}
    ) where T
        @boundscheck _checkrowbounds(base, rows)
        new(base, rows)
    end
end

RowProjectionMatrix(
    base::AbstractArray{T, 2},
    rows::Vector{Int}
) where T = RowProjectionMatrix{T}(base, rows)

RowProjectionMatrix(
    base::AbstractArray{T, 2},
    rows::Vararg{Int, N}
) where {T, N} = RowProjectionMatrix(base, collect(rows))

@inline Base.size(
    M::RowProjectionMatrix{T}
) where T = (length(M.rows), size(M.base)[2])

@inline Base.getindex(
    M::RowProjectionMatrix{T},
    I::Vararg{Int, 2}
) where T = Base.getindex(M.base, M.rows[I[1]], I[2])

@inline Base.setindex!(
    M::RowProjectionMatrix{T},
    v::Any,
    I::Vararg{Int, 2}
) where T = Base.setindex!(M.base, v, M.rows[I[1]], I[2])

function _checkrowbounds(
    base::Union{AbstractArray{T, 1}, AbstractArray{T, 2}},
    rows::Vector{Int}
) where T
    for row ∈ rows
        checkbounds(base, row, :)
    end
end
