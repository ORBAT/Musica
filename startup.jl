using TestItems, Test, Transducers, StaticArrays, Evolutionary, Revise, BenchmarkTools

includet("src/Musica.jl")
##includet("src/CA.jl")

function new_state(row_len)
  let bla = @MVector zeros(Int, row_len)
    bla[1] = 1
    SVector(bla)
  end
end

test_state = Musica.Row{2}(new_state(8))

test_ca = Musica.DiscreteCA{2}(110)
test_ca2 = Musica.DiscreteCA{2,1}(54)

# r=Musica.Row{2}(@SVector [1,2,3,4])