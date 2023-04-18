module Musica
include("transformations.jl")
include("macros.jl")

include("CA.jl")
export DiscreteCA, Row

include("Neuron.jl")
export CANeuron

end

