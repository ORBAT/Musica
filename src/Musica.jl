module Musica

using Base: @propagate_inbounds

###### HOX FIXME: "backport" julian masterissa olevista muutoksista, ettei viewien iterointi ei oo hidasta.
# ks https://github.com/JuliaLang/julia/pull/48720
if VERSION < v"1.9.2"
  Base.checkindex(::Type{Bool}, inds::Base.IdentityUnitRange, i::Real) = Base.checkindex(Bool, inds.indices, i)
  Base.checkindex(::Type{Bool}, inds::Base.OneTo{T}, i::T) where {T<:Base.BitInteger} = unsigned(i) ≤ unsigned(last(inds))
end

include("macros.jl")
include("collection_utils.jl")
include("function_utils.jl")
include("numerical_utils.jl")
include("parsing.jl")
include("ca.jl")
include("Neuron.jl")
include("optimize.jl")

include("./GA/GA.jl")

end

