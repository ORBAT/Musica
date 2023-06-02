module GA
using StaticArrays
#= ################### NOTE muistiinpanoja

HOX: POPULAATIOSSA VOI OLLA ERI PITUSIA GENOMEJA!!!! Eli populaatio ei voi olla vaan m × N matriisi
=#

  struct _State{N}
    population::SVector{N, BitVector}

    """
    Index of best solution so far
    """
    best_idx::Int
    generation::Int
  end

  State = _State
end