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
- `fitness_fn::indiv -> Float64`. EI `row` koska jatkossa voi haluta että esim. genomin pituus tmv vaikuttaa fitnessiin
- `genotype_parser::genome -> indiv`
- paluuarvo: genome -> Float64
"""
@inline function to_obj_fn(genotype_parser::Function, fitness_fn::Function)
  # HOX: DEPREKOITU
  function obj_fn(genome)
    # _ on genome:istä consumeamatta jääneet bitit
    (_, indiv) = genome |> genotype_parser
    indiv |> fitness_fn
  end
end

"""
- `result_generator = indiv::Fn -> (wanted::Number[], Vector{Row})`. Ottaa yksilön, ajaa sen läpi jotain inputtia ja pullauttaa ulos sekä , että resultin eli listan rivejä. Luodaan funkkarilla jonka tyyppi on `input_data -> indiv -> Vector{Row}` (`input_data` ei välttis ole sama kuin `wanted`)
- `fitness_fn = wanted::Number[] -> Vector{Row} -> Float64`
"""
@inline function to_obj_fn(genotype_parser_fn, result_generator_fn, fitness_fn)
  function obj_fn(bits)
    # HOX: tässä mallissa result_generator_fn:n ja fitness_fn:n välillä on riippuvuus. Esim se samplaava obj fun, jossa StatsBase.rmsd(result, wanted[idxs])
    # TODO: tää ratkasu että result_generator_fn palauttaa myös wanted-Arrayn on kyllä vähän vitusta, mutta menköön ny toistaseks
    fitness_fn((bits |> genotype_parser_fn |> _right |> result_generator_fn)...)
  end
end

# @inline function make_fitness_function(output_mapper_fn::Function=row_from_gray, stats_fn::Function=StatsBase.rmsd)
#   function fitness_fn(wanted, row)
#     result = row |> output_mapper_fn
#     stats_fn(result, wanted)
#   end
# end

gray_enc_dec() = num_to_gray_row, row_from_gray

function sampled_result_generator(wanted::T; state_bits=16, sequence_len=3, n_samples=6) where {T<:AbstractArray}
  start_idx_range = 1:(length(wanted)-sequence_len)
  _n_samples = min(length(start_idx_range), n_samples)
  function sampled_result(indiv)
    to_ranges = Map(start_idx -> start_idx:start_idx+sequence_len) |> Cat() |> Unique()
    start_idxs = rand(start_idx_range, _n_samples)
    idxs = start_idxs |> to_ranges
    inp = idxs |> Map(num_to_gray_row)
    result = inp |> Map(indiv) |> collect

  end
end

@inline _right((_, r)) = r
@inline _right(_, r) = r

@testitem "to_obj_fn(gen_parse_fn, res_gen_fn, fit_fn)" begin
  using StaticArrays
  indiv_bits = digits(110; base=2, pad=8)
  _ca = Musica.DiscreteCA{2}(110)
  _wanted = [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  function _parserfn(bits)
    if bits == indiv_bits
      (Int[], _ca)
    else
      (bits, nothing)
    end
  end

  function _res_gen(indiv)
    (_wanted, [indiv(Row{2}(@SVector [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))])
  end

  function _fit_fn(wanted, rows)
    rows == [wanted] ? 0.0 : 1.0
  end

  @test Musica.to_obj_fn(_parserfn, _res_gen, _fit_fn)(indiv_bits) == 0

  #=   state = Row{2}(@SVector [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
  ca = DiscreteCA{2}(110)

  @test ca(state) == [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  @inferred(ca(state)) =#

end

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

function gray_seq_sample_fitness_fn(wanted::T; state_bits::Int=16, sequence_len=4) where {T<:AbstractArray}
  start_idx = rand(1:length(wanted)-sequence_len)

  idxs = start_idx:start_idx+sequence_len
  inp = idxs |> Map(num_to_gray_row)
  state_max_val = 2^state_bits - 1
  _normalize_output = @£ _normalize_num(state_max_val)
  # NOTE: miksi tää kusee jos tähän heittää indiv::Function ????
  ## --> typeof(indiv) = StaticArraysCore.SVector{32, CANeuron{2, 16}}
  ## joka ei oo Function, mutta jolle sattumoisin on määritelty (bla::JokuTyyppi)(state). Go fucking figure.
  function fitness(indiv)
    result = inp |> Map(_normalize_output ∘ row_from_gray ∘ indiv) |> collect
    StatsBase.rmsd(result, wanted[idxs])
  end
end


# HOX: hitaampi ku ei-parallelisoitu versio...
function _gray_multi_seq_sample_fitness_fn_folds(wanted::T; state_bits::Int=16, sequence_len=3, n_samples=5) where {T<:AbstractArray}
  start_idx_range = 1:(length(wanted)-sequence_len)
  max_samples = length(start_idx_range)
  state_max_val = 2^state_bits - 1
  _normalize_output = @£ _normalize_num(state_max_val)
  # NOTE: miksi tää kusee jos tähän heittää indiv::Function ????
  ## --> typeof(indiv) = StaticArraysCore.SVector{32, CANeuron{2, 16}}
  ## joka ei oo Function, mutta jolle sattumoisin on määritelty (bla::JokuTyyppi)(state). Go fucking figure.
  _n_samples = min(max_samples, n_samples)
  function fitness(indiv)
    to_ranges = Map(start_idx -> start_idx:start_idx+sequence_len) |> Cat()
    start_idxs = rand(start_idx_range, _n_samples)
    idxs = start_idxs |> to_ranges |> collect
    result = Folds.map(_normalize_output ∘ row_from_gray ∘ indiv ∘ num_to_gray_row, idxs)
    StatsBase.rmsd(result, wanted[idxs])
  end
end

function gray_multi_seq_sample_fitness_fn(wanted::T; state_bits::Int=16, sequence_len=3, n_samples=6) where {T<:AbstractArray}
  start_idx_range = 1:(length(wanted)-sequence_len)
  max_samples = length(start_idx_range)
  state_max_val = 2^state_bits - 1
  _normalize_output = @£ _normalize_num(state_max_val)
  # HOX: miksi tää kusee jos tähän heittää indiv::Function ????
  ## --> typeof(indiv) = StaticArraysCore.SVector{32, CANeuron{2, 16}}
  ## joka ei oo Function, mutta jolle sattumoisin on määritelty (bla::JokuTyyppi)(state). Go fucking figure.
  _n_samples = min(max_samples, n_samples)
  function fitness(indiv)
    to_ranges = Map(start_idx -> start_idx:start_idx+sequence_len) |> Cat() |> Unique()
    start_idxs = rand(start_idx_range, _n_samples)
    idxs = start_idxs |> to_ranges
    inp = idxs |> Map(num_to_gray_row)
    result = inp |> Map(_normalize_output ∘ row_from_gray ∘ indiv) |> collect
    StatsBase.rmsd(result, wanted[idxs|>collect])
  end
end

## NOTE: näissä mun objective fn:issä yleensä osa joka ottaa input bitit ja tekee niistä jonkun fenotyypin (tässä tapauksessa 
## funktion), ja sit osa joka hieroo sitä training dataa (Map(num_to_gray_row)), ajaa sen sen fenotyypin läpi, ja sit hieroo 
## sitä fenotyypin outputtia (Map(@£ _normalize_num(state_max_val)))
##
## NOTE NOTE: itse asiassa se on jotain suuntaan:
##    (_, indiv) = bits |> genotype_parser
##    inp |> input_mapper |> indiv |> ouput_mapper |> fitness_fn

@inline function _fitness_fn_parallel(fn::Function)
  function fitness_par(input)
    Folds.map(fn, eachrow(input))
  end
end

_row_width()::Int = 16
_bits_per_generation()::Int = 7
_pop_size()::Int = 800
_bits_per_stack_size()::Int = 5

_test_wanted_output(num_cycles=3, scale_factor=2) = _normalize([sin(x / scale_factor) for x = 0:floor((num_cycles * scale_factor)π)])
_test_wanted_output_cos(num_cycles=3, scale_factor=2) = _normalize([cos(x / scale_factor) for x = 0:floor((num_cycles * scale_factor)π)])
_test_wanted_output_tan(num_cycles=3, scale_factor=2) = _normalize([tan(x / scale_factor) for x = 0:floor((num_cycles * scale_factor)π)])

## NOTE: tällä hetkellä tää on yllättävän hyvä optimoimaan tätä. CANeuronStack{29}, row_width = 16, bits_per_gen = 3
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
  wanted = _test_wanted_output(6)
  obj_fn = _fitness_fn_parallel(to_obj_fn(_test_parser_dynamic(), gray_multi_seq_sample_fitness_fn(wanted; state_bits=state_bits)))

  ga = GA(
    N=pop_size, information=information, options=options, p_mutation=p_mutation
    # HUOM: N ehkä syytä olla == pop_size? Essentials of Metaheuristics vähän antais ymmärtää näin (Algorithm 32, sivu 45)
    , selection=TournamentSelection(K=2, N=pop_size), termination=Metaheuristics.RelativeFunctionConvergence()
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