using TestItems, Test, Transducers, StaticArrays, Evolutionary, Revise

includet("src/Musica.jl")
##includet("src/CA.jl")

test_state =
  let row_len = 16, bla = @MVector zeros(Int, row_len)
    bla[1] = 1
    bla
  end

test_ca = Musica.DiscreteCA{2,1}(110)