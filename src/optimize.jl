using TestItems, Folds, StatsBase, Random

"""
    normalize(v)

Normalize `x` so that all of its values are between 0.0 and 1.0.

```jldoctest
julia> normalize([0 10 5])
1×3 Matrix{Float64}:
 0.0  1.0  0.5

julia> normalize([0 0 0])
1×3 Matrix{Float64}:
 0.0  0.0  0.0

julia> normalize([5 5 5])
1×3 Matrix{Float64}:
 1.0  1.0  1.0
```
"""
function normalize(x)
  (_min, _max) = extrema(x)
  if zero(_min) == _min == _max
    return zeros(Float64, size(x))
  end
  _diff = _max - _min
  if _diff == zero(_diff)
    ones(Float64, size(x))
  else
    (x .- _min) ./ _diff
  end
end
export normalize


@inline _right((_, r)) = r
@inline _right(_, r) = r

@inline normalize_num(n, max_val) = n / max_val

export normalize_num

function create_fitness_fn(fn=StatsBase.rmsd, output_mapper=Map(@<(normalize_num(2^_row_width() - 1)) ∘ row_from_gray))
  @inline function fitness_fn(wanted, result)
    _wanted = wanted |> maybe_collect
    _result = result |> output_mapper |> maybe_collect
    fn(_wanted, _result)
  end
end

export create_fitness_fn

function create_obj_fn(genotype_parser_fn, input_data_gen_fn, result_gen_fn, fitness_fn)
  @inline return function obj_fn(bits)
    (wanted, input) = input_data_gen_fn()
    # HUOM: _ on ylijääneet bitit
    (_, indiv) = bits |> genotype_parser_fn
    result = result_gen_fn(input, indiv)
    fitness_fn(wanted, result)
  end
end

export create_obj_fn

# gray_inp_out(w::Type{Val{width}}=Val{16}) where {width} = @<(num_to_gray_row(w)), (@<(_normalize_num(2^width - 1)) ∘ row_from_gray)

function input_based_result_gen(input_mapper=@<(num_to_gray_row(Val{_row_width()})))
  @inline function _input_based_result_gen(input, indiv)
    input |> Map(indiv ∘ input_mapper)
  end
end

export input_based_result_gen

function full_data_generator(wanted::T) where {T<:AbstractArray}
  @inline function _full_data_generator()
    (wanted, 1:length(wanted))
  end
end

export full_data_generator

#HOX: sämpläys tuntuu antavan paskoja tuloksia aika herkästi sit kuitenkin, ainakin näin pienellä datasetillä.
# HOX HOX: ehkä isommalla datasetillä ja sequence_len ≥ 30 vois olla ihan jees? Nykynen testidatasetti on 32 pitkä, ja full_data_generator:illa
#   sai parem
function sampled_data_generator(wanted::T; sequence_len=6, n_samples=3, rng=nothing) where {T<:AbstractArray}
  start_idx_range = 1:(length(wanted)-(sequence_len-1))
  _n_samples = min(length(start_idx_range), n_samples)
  to_ranges = MapCat(start_idx -> start_idx:start_idx+(sequence_len-1)) |> Unique()
  # HUOM: palauttaa (wanted, input)
  @inline function _sampled_data_generator()
    _rng = if isnothing(rng)
      Random.default_rng()
    else
      rng
    end
    start_idxs = rand(_rng, start_idx_range, _n_samples)
    idxs = start_idxs |> to_ranges
    masked_wanted = (wanted,) |> MapCat(w -> w[idxs|>collect])
    (masked_wanted, idxs)
  end
end

export sampled_data_generator

## HOX: näissä mun objective fn:issä yleensä osa joka ottaa input bitit ja tekee niistä jonkun fenotyypin (tässä tapauksessa 
## funktion), ja sit osa joka hieroo sitä training dataa (Map(num_to_gray_row)), ajaa sen sen fenotyypin läpi, ja sit hieroo 
## sitä fenotyypin outputtia (Map(@< _normalize_num(state_max_val)))
##
## HOX HOX: itse asiassa se on jotain suuntaan:
##    (_, indiv) = bits |> genotype_parser
##    inp |> input_mapper |> indiv |> ouput_mapper |> fitness_fn

@inline function _obj_fn_to_parallel(fn::Function)
  @inline function objfn_par(input)
    Folds.map(fn, eachrow(input))
  end
end

_row_width()::Int = 16
#HOX: jos _bits_per_generation > 5 niin tuntuu että laatu kärsii, resultit on lähinnä suoraa viivaa.
# 5 b/gen ja 5 b/CANeuronStack size ja full_data_generator on tuottanu ihan OK tuloksia. Pari sellasta yhen tai kahen CA:n stackia jotka on ollu yllättävän hyviä
_bits_per_generation()::Int = 7
_bits_per_stack_size()::Int = 6
_pop_size()::Int = 500

_StackType() = CANeuronStack{16,2,_row_width()}

_test_parser(;bits_per_gen=_bits_per_generation()) = Musica.parser(_StackType(); bits_per_gen=bits_per_gen)
_test_parser_dynamic() = parser(CANeuronStack;
  bits_per_gen=_bits_per_generation(),
  bits_per_stack_size=_bits_per_stack_size(),
  state_width=_row_width()
)
_test_parser_bits_required() = parser_bits_required(_StackType(); bits_per_gen=_bits_per_generation())

_test_parser_bits_required_dyn() = Musica.parser_bits_required(CANeuronStack; bits_per_gen=_bits_per_generation(), bits_per_stack_size=_bits_per_stack_size())


_test_wanted_output(num_cycles=3, scale_factor=2) = normalize(sin(x / scale_factor) for x = 0:floor((num_cycles * scale_factor)π))
_test_wanted_output_cos(num_cycles=3, scale_factor=2) = normalize(cos(x / scale_factor) for x = 0:floor((num_cycles * scale_factor)π))
_test_wanted_output_tan(num_cycles=3, scale_factor=2) = normalize(tan(x / scale_factor) for x = 0:floor((num_cycles * scale_factor)π))

## HUOM: tällä hetkellä tää on yllättävän hyvä optimoimaan tätä. CANeuronStack{29}, row_width = 16, bits_per_gen = 3
function _test_wanted_output_rastr(D=10, step=0.5)
  rastr(x) = sum(x .* x - 10cos.(2π * x))
  normalize(rastr(x) for x = -5:step:5)
end


