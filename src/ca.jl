module CA
using WhereTraits, Static, TestItems
using Base: @propagate_inbounds
using ..Musica

"""
Abstract type for CAs.

To implement a new CA, you have to implement the following methods:

- `CA.apply_ca!(ca, inp)`
- `CA.DomainType(::Type{YourCA})` if you need something else than `Discrete(2)`. If your CA "wraps" another CA (like [`Stateful`](@ref)), you don't need this. See below

Optional:

- `CA.neighborhood_size(::Type{YourCA})`. TODO: is this actually needed?
- `CA.HasParent(::Type{YourCA})`. If your CA "wraps" another CA, you should implement this and return `CA.ParentType{YourCAsParent}`
`

"""
abstract type Abstract <: Function end

"""
    ca = CA.Elementary(110)
    ca(inp)

Apply `ca` to `inp`. Same as `apply_ca(ca, inp)`
"""
@inline function (ca::Abstract)(inp)
  apply_ca(ca, inp)
end

"""
    apply_ca(ca, inp)

Apply `ca` to `inp`. Calls `apply_ca!(ca, similar_copy(inp))`
"""
@inline (apply_ca(ca::Abstract, inp::T)::T) where {T} = apply_ca!(ca, similar_copy(inp))

apply_ca!(ca::Abstract, @nospecialize(inp)) = error("apply_ca! not implemented for ", typeof(ca))

neighborhood_size(radius) = radius * 2 + 1

abstract type DomainType end

struct Discrete{NStates} <: DomainType end
Base.@constprop :aggressive @inline Discrete(n_states::Integer) = Discrete{n_states}()

@inline Static.known(::Type{Discrete{NStates}}) where {NStates} = NStates

abstract type HasParent end

struct ParentType{T} <: HasParent end
ParentType(::Type{T}) where {T} = ParentType{T}()

struct NoParent <: HasParent end

"""
    HasParent(T)
Returns `ParentType{A}` if `T` has a parent CA of type `A`. Otherwise returns `NoParent`
"""
HasParent(::Type{<:Abstract}) = NoParent()

struct Continuous <: DomainType end

DomainType(@nospecialize(T::Type)) = error("no DomainType for ", T, ". Need a subtype of CA.Abstract")
"""
    DomainType(T)
Returns `Discrete{NStates}` if `T` is a discrete CA with `NStates` states. Otherwise returns `Continuous`.

If `T` has a parent CA of type `A` and implements `HasParent`, `DomainType(T)` returns `DomainType(A)`.
"""
@inline DomainType(_::Type{T}) where {T<:Abstract} = DomainType(T |> HasParent, T) 
@inline DomainType(x) = x |> typeof |> DomainType

DomainType(::ParentType{P}, @nospecialize(T)) where {P} = DomainType(P)
DomainType(::NoParent, @nospecialize(T)) = error("no DomainType defined for ", T)

@inline isdiscrete(::Type{T}) where {T<:Abstract} = DomainType(T) <: CA.Discrete
@inline isdiscrete(v) = v |> typeof |> isdiscrete

## HUOM: hölmö tapa käyttää traitteja ylipäätään, plus @traits lisää kutsuun +50ns, mikä on aika vitusta
# @inline @traits isdiscrete(_::Type{T}) where {T<:Abstract, DomainType(T)::CA.Discrete} = true
# @inline @traits isdiscrete(_::Type{T}) where {T<:Abstract} = false


include("row.jl")
include("eca.jl")
include("transforming_cas.jl")

end

export CA

import .CA: Row

export Row