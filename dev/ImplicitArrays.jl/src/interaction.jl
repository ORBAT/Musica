"""
    InteractionFunction{R, C, T}

Abstract base type of all interaction functions `R × C → T`.
"""
abstract type InteractionFunction{R, C, T} end

"""
    struct ConstInteractionFunction{R, C, T} <: InteractionFunction{R, C, T}

Interaction function `R × C → T` that ignores its arguments and returns a fixed value.

# Constructor
    ConstInteractionFunction{R, C, T}(val)

Create a constant interaction function that always returns `val`.

# Examples
```jldoctest; setup = :(using ImplicitArrays)
julia> f = ConstInteractionFunction{Float64, Float64, Int64}(42);

julia> f(1.0, 1.5)
42
```
"""
struct ConstInteractionFunction{R, C, T} <: InteractionFunction{R, C, T}
    val::T
end
(f::ConstInteractionFunction{R, C, T})(x::R, y::C) where {R, C, T} = f.val

"""
    GenericInteractionFunction{R, C, T} <: InteractionFunction{R, C, T}

Interaction function `R × C → T` acting as a type-safe wrapper for a given function.

# Constructor
    GenericInteractionFunction{R, C, T}(fun)

Create an interaction function from the given function `fun`.

# Examples
```jldoctest; setup = :(using ImplicitArrays)
julia> f = GenericInteractionFunction{Int64, Int64, Int64}(+); f(9, 3)
12

julia> g = GenericInteractionFunction{Int64, Int64, Float64}(/); g(9, 3)
3.0

julia> h = GenericInteractionFunction{String, Int64, String}(repeat); h("abc", 3)
"abcabcabc"
```

!!! note
    The interaction function can only be evaluated if there is a method `fun(::R, ::C)` that
    returns a value of type `T`. Otherwise, a `MethodError` or `TypeError` is thrown.
"""
struct GenericInteractionFunction{R, C, T} <: InteractionFunction{R, C, T}
    f::Function
end
(f::GenericInteractionFunction{R, C, T})(x::R, y::C) where {R, C, T} = f.f(x, y)::T

"""
    InteractionMatrix{T, R, C, F <: InteractionFunction{R, C, T}} <: AbstractArray{T, 2}

Interaction matrix with elements of type `T`, generated from row elements of type `R`, column
elements of type `C`, and an interaction function `F: R × C → T`.

# Constructors
    InteractionMatrix(rowelems, colelems, interact)
    InteractionMatrix{T}(rowelems, colelems, interact)

Create an interaction matrix for the given row and column element arrays as well as an interaction
 function.

    InteractionMatrix(rowelems, colelems, val)

Create an interaction matrix for the given (yet unused) row and column element arrays and a
constant interaction function always returning `val`. In this form, the interaction matrix acts
as a replacement for a two-dimensional [`FixedValueArray`](@ref).

# Examples
```jldoctest; setup = :(using ImplicitArrays)
julia> InteractionMatrix{Int64}([1, 2, 3], [10, 20, 30], +)
3×3 InteractionMatrix{Int64, Int64, Int64, GenericInteractionFunction{Int64, Int64, Int64}}:
 11  21  31
 12  22  32
 13  23  33

julia> InteractionMatrix([1, 2, 3], [10, 20, 30], 42)
3×3 InteractionMatrix{Int64, Int64, Int64, ConstInteractionFunction{Int64, Int64, Int64}}:
 42  42  42
 42  42  42
 42  42  42

julia> struct DivFun <: InteractionFunction{Int, Int, Float64} end

julia> (::DivFun)(x::Int, y::Int) = x / y

julia> InteractionMatrix([10, 20, 30], [5, 2, 1], DivFun())
3×3 InteractionMatrix{Float64, Int64, Int64, DivFun}:
 2.0   5.0  10.0
 4.0  10.0  20.0
 6.0  15.0  30.0
```
"""
struct InteractionMatrix{T, R, C, F <: InteractionFunction{R, C, T}} <: AbstractArray{T, 2}
    rowelems::Array{R, 1}
    colelems::Array{C, 1}
    interact::F

    @inline function InteractionMatrix(
        rowelems::Array{R, 1},
        colelems::Array{C, 1},
        interact::F
    ) where {T, R, C, F <: InteractionFunction{R, C, T}}
        new{T, R, C, F}(rowelems, colelems, interact)
    end
end

@inline InteractionMatrix{T}(
    rowelems::Array{R, 1},
    colelems::Array{C, 1},
    interact::Function
) where {T, R, C} = InteractionMatrix(
    rowelems,
    colelems,
    GenericInteractionFunction{R, C, T}(interact)
)

@inline InteractionMatrix(
    rowelems::Array{R, 1},
    colelems::Array{C, 1},
    val::T
) where {T, R, C} = InteractionMatrix(
    rowelems,
    colelems,
    ConstInteractionFunction{R, C, T}(val)
)

@inline Base.size(
    A::InteractionMatrix{T}
) where T = (length(A.rowelems), length(A.colelems))

@inline Base.getindex(
    A::InteractionMatrix{T},
    I::Vararg{Int, 2}
) where T = A.interact(A.rowelems[I[1]], A.colelems[I[2]])::T

@inline Base.setindex!(
    A::InteractionMatrix{T},
    ::Any,
    ::Int
) where T = _throw_canonical_error("setindex! not defined for ", typeof(A))
