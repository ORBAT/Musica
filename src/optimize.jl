using GrayCode, TestItems, Test, Folds, Metaheuristics, StatsBase

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
function _normalize(x)
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

@inline _normalize_num(n, max_val) = n / max_val

"""
TODO: enkuksi



Palauttaa tavoitefunktion, joka ottaa raakabittejä (tmv) ja
- parsii yksilön `indiv` fenotyypin biteistä `genotype_parser`:illa
- ajaa `fitness_fn(indiv)`

Tyypit:
- `indiv::row -> row` (eli _ainakin_ tyyppi joka käyttäytyy ku funktio `row -> row`)
- `fitness_fn::indiv -> Float64`. HOX: ei `row` koska jatkossa voi haluta että esim. genomin pituus tmv vaikuttaa fitnessiin
- `genotype_parser::genome -> indiv`
- paluuarvo: genome -> Float64
"""
@inline function to_obj_fn(genotype_parser::Function, fitness_fn::Function)
  function obj_fn(bits)
    # _ on bits:istä consumeamatta jääneet bitit
    (_, indiv) = bits |> genotype_parser
    indiv |> fitness_fn
  end
end

##### TODO: testit
# @testitem "to_obj_fn" begin
#   ca = Musica.DiscreteCA{2}(110)
#   input = Row{2}(@SVector [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
#   expect_output = [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

#   genome_bits = digits(110)

#   parser = bits -> bits != genome_bits ? error("weird parser input", bits) : ca
#   fitness_fn = indiv -> input |> indiv
# end

function gray_both_obj_fn_for(wanted::T; state_bits::Int=16) where {T<:AbstractArray}
  len_wanted = length(wanted)
  inp = 1:len_wanted |> Map(num_to_gray_row)
  state_max_val = 2^state_bits - 1
  _normalize_output = @£ _normalize_num(state_max_val)
  function f(indiv)
    result = inp |> Map(_normalize_output ∘ row_from_gray ∘ indiv) |> collect
    StatsBase.rmsd(result, wanted)
  end
end

function gray_seq_sample_fitness_fn(wanted::T; state_bits::Int=16, n_samples=4) where {T<:AbstractArray}
  start_idx = rand(1:length(wanted)-n_samples)
  idxs = start_idx:start_idx+n_samples
  inp = idxs |> Map(num_to_gray_row)
  state_max_val = 2^state_bits - 1
  _normalize_output = @£ _normalize_num(state_max_val)
  # TODO: miksi tää kusee jos tähän heittää indiv::Function ????
  ## --> typeof(indiv) = StaticArraysCore.SVector{32, CANeuron{2, 16}}
  ## joka ei oo Function, mutta jolle sattumoisin on määritelty (bla::JokuTyyppi)(state). Go fucking figure.
  function fitness(indiv)
    result = inp |> Map(_normalize_output ∘ row_from_gray ∘ indiv) |> collect
    StatsBase.rmsd(result, wanted[idxs])
  end
end

## HOX: näissä mun objective fn:issä yleensä osa joka ottaa input bitit ja tekee niistä jonkun fenotyypin (tässä tapauksessa 
## funktion), ja sit osa joka hieroo sitä training dataa (Map(num_to_gray_row)), ajaa sen sen fenotyypin läpi, ja sit hieroo 
## sitä fenotyypin outputtia (Map(@£ _normalize_num(state_max_val)))
##
## HOX HOX: itse asiassa se on jotain suuntaan:
##    (_, indiv) = bits |> genotype_parser
##    inp |> input_mapper |> indiv |> ouput_mapper |> fitness_fn

@inline function _fitness_fn_parallel(fn::Function)
  function fitness_par(input)
    Folds.map(fn, eachrow(input))
  end
end

_row_width()::Int = 16
_bits_per_generation()::Int = 7
_pop_size()::Int = 1500
_bits_per_stack_size()::Int = 5

_test_wanted_output(num_cycles=3, scale_factor=2) = _normalize([sin(x / scale_factor) for x = 0:floor((num_cycles * scale_factor)π)])
_test_wanted_output_cos(num_cycles=3, scale_factor=2) = _normalize([cos(x / scale_factor) for x = 0:floor((num_cycles * scale_factor)π)])
_test_wanted_output_tan(num_cycles=3, scale_factor=2) = _normalize([tan(x / scale_factor) for x = 0:floor((num_cycles * scale_factor)π)])

## HOX: tällä hetkellä tää on yllättävän hyvä optimoimaan tätä. CANeuronStack{29}, row_width = 16, bits_per_gen = 3
function _test_wanted_output_rastr(D=10, step=0.5)
  rastr(x) = 10D + sum(x .* x - 10cos.(2π * x))
  _normalize([rastr(x) for x = -5:step:5])
end

_StackType() = CANeuronStack{32,2,_row_width()}

_test_parser() = Musica.parser(_StackType(); bits_per_gen=_bits_per_generation())
_test_parser_dynamic() = parser(CANeuronStack;
  bits_per_gen=_bits_per_generation(),
  bits_per_stack_size=_bits_per_stack_size(),
  state_width=_row_width()
)
_test_parser_bits_required() = parser_bits_required(_StackType(); bits_per_gen=_bits_per_generation())

_test_parser_bits_required_dyn() = Musica.parser_bits_required(CANeuronStack{2^_bits_per_stack_size(),2,_row_width()}; bits_per_gen=_bits_per_generation()) + 10


## HUOM: _Neverstop ja default_stop_check-metodi on klugeja joilla yritän estää vitun Metaheuristicsia luovuttamasta kesken kaiken

struct _Neverstop <: Metaheuristics.AbstractTermination end

function Metaheuristics.stop_check(population, criteria::_Neverstop)
  false
end

# function Metaheuristics.default_stop_check(status, information, options)
#   Metaheuristics.time_stop_check(status, information, options)
# end


function _do_opt(; f_calls_limit=typemax(Int), time_limit=60 * 0.5, p_mutation=64e-4)

  pop_size = _pop_size()

  state_bits = _row_width()

  information = Information(f_optimum=0.0)
  options = Options(f_tol=eps(),
    time_limit=time_limit,
    parallel_evaluation=true,
    store_convergence=true,
    iterations=typemax(Int64),
    f_calls_limit=f_calls_limit
  )
  wanted = _test_wanted_output()
  obj_fn = _fitness_fn_parallel(to_obj_fn(_test_parser_dynamic(), gray_both_obj_fn_for(wanted; state_bits=state_bits)))

  ga = GA(
    N=pop_size
    ,information=information
    ,options=options
    , p_mutation=p_mutation
    # HUOM: isompi N ja pienempi K on hyväksi explorationille
    , selection=TournamentSelection(K=2, N=pop_size*2)
    , termination=Metaheuristics.RelativeFunctionConvergence()
    ## HOX: GenerationalReplacement ei vittu toimi jos tourn N>pop_size
    # , environmental_selection=Metaheuristics.GenerationalReplacement()
    , environmental_selection=Metaheuristics.ElitistReplacement()
    # ; termination=_Neverstop()
  )

  num_bits = _test_parser_bits_required_dyn() #Musica.parser_bits_required(_Stack; bits_per_gen=bpg)

  optimize(obj_fn, BitArraySpace(num_bits), ga)
end

function get_best_at(fn, opt_result, parser)
  all_fitnesses = Folds.map(to_obj_fn(parser, fn), map(x -> x.x, opt_result.population))
  _min = minimum(all_fitnesses)
  best_idx = findfirst(≈(_min), all_fitnesses)
  opt_result.population[best_idx].x
end