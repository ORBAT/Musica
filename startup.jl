using TestItems, Test, Transducers, StaticArrays, Evolutionary, Revise, BenchmarkTools

includet("src/Musica.jl")
##includet("src/CA.jl")

function new_state(row_len)
  state = let bla = @MVector zeros(Int, row_len)
    bla[1] = 1
    SVector(bla)
  end
end

test_state = new_state(32)

test_ca = Musica.DiscreteCA{2,1}(110)

r=Musica.Row{2}(@SVector [1,2,3,4])