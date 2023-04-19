module Musica
include("macros.jl")
include("function_utils.jl")

include("CA.jl")
export DiscreteCA, Row

include("Neuron.jl")
export CANeuron

end

