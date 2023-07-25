module CA
using Static, TestItems
using Base: @propagate_inbounds
using ..Musica

"""
Abstract type for CAs.

To implement a new CA, you have to implement the following methods:

  - `CA.apply_ca!(ca, inp)`
  - `CA.DomainType(::Type{YourCA})`. Not needed if your CA "wraps" another CA (like [`Stateful`](@ref)). See note about `CA.HasParent` below

Optional:

  - `CA.HasParent(::Type{YourCA})`. If your CA "wraps" another CA, you should implement this and return `CA.ParentType(YourCAsParentType)`
  - `CA.neighborhood_size(::Type{YourCA})`. TODO: is this actually needed?
"""
abstract type Abstract end

"""
    ca = CA.Elementary(110)
    ca(inp)

Apply `ca` to `inp`. Same as `apply_ca(ca, inp)`
"""
@inline function (ca::Abstract)(inp)
  apply_ca(ca, inp)
end

"""
    apply_ca(ca, inp::T)::T

Apply `ca` to `inp`. Note that it always returns the same type that `inp` is

Calls `apply_ca!(ca, similar_copy(inp))` (`similar` since `inp` might be backed by an immutable type).

TODO: pretty inefficient when `inp` is backed by an immutable type. I guess it's Good Enough™ for a default, and subtypes can define more efficient methods if needed?
"""
@inline (apply_ca(ca::Abstract, inp::T)::T) where {T} = apply_ca!(ca, similar_copy(inp))

apply_ca!(@nospecialize(ca::Abstract), @nospecialize(inp)) =
  error("apply_ca! not implemented for ", typeof(ca))

@inline neighborhood_size(radius) = radius * 2 + 1

abstract type HasParent end

struct ParentType{T} <: HasParent end
ParentType(::Type{T}) where {T} = ParentType{T}()

"""
    HasParent(T)

Returns `ParentType{A}` if `T` has a parent CA of type `A`. Otherwise returns `NoParent`
"""
HasParent(::Type{<:Abstract}) = NoParent()

abstract type DomainType end

struct Continuous <: DomainType end

struct Discrete{NStates} <: DomainType end
Base.@constprop :aggressive @inline Discrete(n_states::Integer) = Discrete{n_states}()

@inline Static.known(::Type{Discrete{NStates}}) where {NStates} = NStates

struct NoParent <: HasParent end

DomainType(@nospecialize(T::Type)) =
  error("no DomainType for ", T, ". Need a subtype of CA.Abstract")
"""
    DomainType(T)

Returns `Discrete{NStates}` if `T` is a discrete CA with `NStates` states. Otherwise returns `Continuous`.

If `T` implements `HasParent` and returns `ParentType{A}`, by default `DomainType(T)` returns `DomainType(A)`.
"""
@inline DomainType(_::Type{T}) where {T<:Abstract} = _DomainType(T |> HasParent, T)
@inline DomainType(x) = x |> typeof |> DomainType

_DomainType(::ParentType{P}, @nospecialize(_)) where {P} = DomainType(P)
_DomainType(::NoParent, @nospecialize(T)) = error("no DomainType defined for ", T)

@inline isdiscrete(::Type{T}) where {T<:Abstract} = DomainType(T) <: CA.Discrete
@inline isdiscrete(v) = v |> typeof |> isdiscrete

include("row.jl")
include("eca.jl")
include("transforming_cas.jl")

end

export CA

using .CA: Row

export Row