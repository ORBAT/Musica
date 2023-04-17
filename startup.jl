using TestItems, Test, Transducers, StaticArrays, Evolutionary, Revise

includet("src/Musica.jl")
##includet("src/CA.jl")

function new_state(row_len)
  @SVector ones(Int, row_len)
end

test_state = new_state(32)

test_ca = Musica.DiscreteCA{2,1}(110)