module Musica

###### HOX FIXME: "backport" julian masterissa olevista muutoksista, ettei viewien iterointi ei oo hidasta.
if VERSION < v"1.9.2"
  Base.checkindex(::Type{Bool}, inds::Base.IdentityUnitRange, i::Real) = Base.checkindex(Bool, inds.indices, i)
  Base.checkindex(::Type{Bool}, inds::Base.OneTo{T}, i::T) where {T<:Base.BitInteger} = unsigned(i - one(i)) < unsigned(last(inds))
end

include("macros.jl")
include("collection_utils.jl")
include("function_utils.jl")
include("parsing.jl")
include("discrete_ca.jl")
include("CA.jl")
include("Neuron.jl")
include("optimize.jl")

include("./GA/GA.jl")

end

