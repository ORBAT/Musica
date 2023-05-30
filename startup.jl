using TestItems, Test, Transducers, StaticArrays, Revise, BenchmarkTools, Metaheuristics, StatsBase

# BenchmarkTools.DEFAULT_PARAMETERS.samples = 30000

includet("src/Musica.jl")

using .Musica

function new_state(::Type{Val{L}}) where {L}
  let bla = zeros(Int, L)
    bla[1] = 1
    Row{2}(SizedVector{L}(bla))
  end
end

function new_state(::Val{L}) where {L}
  new_state(Val{L})
end

new_state(v::Integer) = new_state(Val(v))

test_state=new_state(Val{16})
n_generations=5

test_ca = DiscreteCA{2}(110)
test_ca2 = DiscreteCA{2,1}(54)

test_can = CANeuron{2,16}(test_ca, n_generations)
test_can2 = CANeuron{2,16}(test_ca2, Int(floor(n_generations/2)))

test_stack = CANeuronStack{2,2,16}(test_can,test_can2)