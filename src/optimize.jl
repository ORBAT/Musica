using GrayCode, TestItems, Test, Folds, Metaheuristics

"""
    _normalize(v)

Normalize `x` so that all of its values are between 0.0 and 1.0.

```jldoctest
julia> Musica._normalize([0 10 5])
1×3 Matrix{Float64}:
 0.0  1.0  0.5

julia> Musica._normalize([0 0 0])
1×3 Matrix{Float64}:
 0.0  0.0  0.0

julia> Musica._normalize([5 5 5])
1×3 Matrix{Float64}:
 1.0  1.0  1.0
```
"""
@inline function _normalize(x)
  (_min, _max) = extrema(x)
  if _min == _max == 0
    return zeros(Float64, size(x))
  end
  _diff = _max - _min
  if _diff == 0
    ones(Float64, size(x))
  else
    (x .- _min) ./ _diff
  end
end

@inline num_from_gray(n) = Integer(reinterpret(Gray64, n))

function _obj_fn_parallel(fn::Function)
  function f_par(input)
    Folds.map(fn, eachrow(input))
  end
end

# _state_bits() = 16
# _bits_per_gen() = 3


# function optimize(fn)
#   _Stack = CANeuronStack{32, 2, _state_bits()}

#   information = Information(f_optimum=0.0)
#   options = Options(f_tol=0.05,
#     time_limit=60.0 * 0.5,
#     # f_calls_limit=8,
#     parallel_evaluation=true,
#     store_convergence=true
#   )
#   Metaheuristics.optimize(fn,
#     BitArraySpace(num_bits),
#     GA(
#       N=1,
#       information=information,
#       options=options,
#       p_mutation=16e-4,
#       # HUOM: isompi N ja pienempi K on hyväksi explorationille
#       selection=TournamentSelection(K=2, N=pop_size * 2)
#       ; termination=Metaheuristics.RelativeFunctionConvergence()
#     ))
# end
