using TestItems, Test, Transducers, StaticArrays, Evolutionary, Revise, BenchmarkTools

BenchmarkTools.DEFAULT_PARAMETERS.samples = 30000

includet("src/Musica.jl")
##includet("src/CA.jl")

using .Musica

function new_state(::Type{Val{L}})::SizedVector{L} where {L}
  state = let bla = zeros(Int, L)
    bla[1] = 1
    SizedVector{L}(bla)
  end
end

function new_state(::Val{L})::SizedVector{L} where {L}
  new_state(Val{L})
end

new_state(v::Integer) = new_state(Val(v))

test_ca = DiscreteCA{2,1}(110)
test_state=Row{2}(new_state(Val{32}))
n_generations=40



test_ca = DiscreteCA{2}(110)
test_ca2 = DiscreteCA{2,1}(54)

# r=Musica.Row{2}(@SVector [1,2,3,4])