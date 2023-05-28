module Musica
include("macros.jl")
include("function_utils.jl")
include("parsing.jl")
include("CA.jl")
export DiscreteCA, Row

include("Neuron.jl")
export CANeuron, CANeuronStack

include("optimize.jl")

end

