
struct Stateful{Len,C<:Abstract,State} <: Abstract
  ca::C
  state::State

  function Stateful(ca::C, initial_state::Row{NStates,Len}) where {NStates,Len,C<:Abstract}
    # TODO: tarkista että initial_state kans toimii ca:n kanssa. Tarvinnee traitteja
    _state = to_mutable(initial_state)
    new{Len,C,typeof(_state)}(ca, _state)
  end
end

HasParent(::Type{<:Stateful{Len,C}}) where {Len,C} = ParentType(C)
# DomainType(::Type{Stateful{Len,C}}) where {Len,C} = DomainType(C)
# neighborhood_size(::Type{Stateful{Len,C}}) where {Len,C} = neighborhood_size(C)

@inline apply_ca!(sca::Stateful{L}, inp::Row{N,W}) where {L,N,W} = apply_ca!(sca.ca, sca.state ⊻ inp)

@inline function update_state!(sca::Stateful{Len}, inp::T) where {Len,NStates,T<:Row{NStates,Len}}
  sca.state .= inp
  sca
end

@inline function update_state(sca::Stateful{Len}, inp::T) where {Len,NStates,T<:Row{NStates,Len}}
  Stateful(sca.ca, inp)
end

function Base.show(io::IO, s::Stateful{Len}) where {Len}
  print(io, "CA.Stateful{Len=", Len, "}")
  print(io, "(", s.ca, ", ", s.state, ")")
end

Base.show(io::IO, ::MIME"text/plain", s::Stateful) = show(io, s)

@testitem "Stateful" begin
  let ca = CA.Elementary(110), init_state = CA.num_to_row(5,Val(16)), test_state = CA.num_to_row(1,Val(16))
    stateful = CA.Stateful(ca, init_state)
    @test stateful(test_state) == ca(init_state ⊻ test_state)
  end
end

"""
    Repeated(ca, times)
CA that repeatedly applies `ca` `times` times. `Repeated(ca, 2)(input) == (ca ∘ ca)(input)`
"""
struct Repeated{CA<:Abstract, T} <: Abstract 
  ca::CA
  times::T
end

DomainType(::Type{Repeated{CA}}) where {CA} = DomainType(CA)

function apply_ca!(rca::Repeated, inp)
  let inner_ca = rca.ca, out = inp
    for _ in Base.oneto(rca.times)
      out = apply_ca!(inner_ca, out)
    end
    out
  end
end

@testitem "Repeated" begin
  let ca = CA.Elementary(110), state = CA.num_to_row(1,Val(16))
    rca = CA.Repeated(ca, 2)
    @test rca(state) == (ca ∘ ca)(state)
  end
end