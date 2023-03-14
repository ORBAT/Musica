module GA
using Base: @propagate_inbounds
include("genome.jl")
include("population_methods.jl")
include("state.jl")
end

export GA