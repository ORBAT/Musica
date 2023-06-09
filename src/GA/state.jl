
using StaticArrays, StructArrays, TestItems, Folds, Random
using ..Musica: _SizedTypes, Maybe
using Printf
using AutoHashEqualsCached

#= ################### NOTE muistiinpanoja

HOX: POPULAATIOSSA VOI OLLA ERI PITUSIA GENOMEJA!!!! Eli populaatio ei voi olla vaan m × N matriisi
Ja pelkästään jo ton takia Metaheuristics ei kyl enää kanna. 
=#

struct Individual{GenomeType<:AbstractArray}
  genome::GenomeType
  fitness::Float64
end

function Base.show(io::IO, indiv::Individual{GT}) where {GT}
  print(io, "Individual(")
  show(io, indiv.genome)
  @printf(io, ", %.5f)", indiv.fitness)
end

@inline fitness(indiv) = indiv.fitness
@inline function set_fitness(indiv, f::Float64)
  indiv.fitness = f
  indiv
end

# function _eval_indiv_fitness!(indiv, obj_fn::Function, genome_mapper::Function)
#   # TODO KYS: vähän kluge, tiiä ees onko tarpeen. Heitä vittuun jahka homma etenee?
#   # @assert isequal(indiv.fitness, Inf) "Evaluating individual that already has a fitness value"
#   set_fitness(indiv, obj_fn(genome_mapper(indiv.genome)))
# end

# HOX: jostain syystä koko paska kippaa jos Individual:illa tekee tän nimitempun.
# UndefVarError: `Individual` not defined
# Individual = _Individual2

#= @inline function Base.hash(a::Individual{GT}, h::UInt) where {GT}
  hash((:Individual), h) |>
  @>(hash(GT)) |>
  @>(hash(a.genome)) |>
  @>(hash(a.fitness))
end

@inline function Base.:(==)(a::Individual, b::Individual)
  isequal(a.fitness, b.fitness) && isequal(a.genome, b.genome)
end =#

Base.@kwdef struct Options
  # kova raja genomin pituudelle
  genome_max_len::Int# = 2048
  initial_genome_min_len::Int# = 256

  codon_size::Integer = 6
  redundant_per_codon::Integer = 2

  mut_segment_mean_len::Int = codon_size # mean segment length in mutations
  mut_segment_stdev::Float64 = 1.5
  mut_codon_p::Float64 = 0.005 # probability that a codon will mutate
  # mut_point_p::Float64 = 0.005
  # mut_ins_p::Float64 = 0.005
  # mut_del_p::Float64 = 0.005
  #=

  mut_rev_p::Float64 # prob. to reverse a segment of max len mut_segment_mean_len
  mut_trans_p::Float64 # translocate a segment

  mut_duplicate_p::Float64
  =#


  objective_fn::Function
  rng::Maybe{Random.AbstractRNG}# = nothing
end

# Options = _Options3

@inline function Base.hash(o::Options, h::UInt)
  # @info "Base.hash(Options)"
  hash(:Options, h) |>
  @>(hash(o.genome_max_len)) |>
  @>(hash(o.initial_genome_min_len)) |> 
  @>(hash(o.codon_size)) |>
  @>(hash(o.redundant_per_codon)) |> 
  @>(hash(o.mut_segment_mean_len)) |>
  @>(hash(o.mut_segment_stdev)) |>
  @>(hash(o.mut_codon_p)) |>
  # @>(hash(o.mut_point_p)) |>
  # @>(hash(o.mut_ins_p)) |>
  # @>(hash(o.mut_del_p)) |> 
  @>(hash(o.objective_fn)) |>
  @>(hash(o.rng))
end

@inline function Base.:(==)(a::Options, b::Options)
  isequal(a.genome_max_len, b.genome_max_len) &&
    isequal(a.initial_genome_min_len, b.initial_genome_min_len) && isequal(a.codon_size, b.codon_size) &&
    isequal(a.redundant_per_codon, b.redundant_per_codon) &&
    isequal(a.mut_segment_mean_len, b.mut_segment_mean_len) &&
    isequal(a.mut_segment_stdev, b.mut_segment_stdev) &&
    isequal(a.mut_codon_p, b.mut_codon_p) &&
    # isequal(a.mut_point_p, b.mut_point_p) &&
    # isequal(a.mut_ins_p, b.mut_ins_p) &&
    # isequal(a.mut_del_p, b.mut_del_p) && 
    isequal(a.objective_fn, b.objective_fn) &&
    isequal(a.rng, b.rng)
end


function _get_rng(o::Options)
  if isnothing(o.rng)
    Random.default_rng()
  else
    o.rng
  end
end

@auto_hash_equals mutable struct State{N,GenomeType<:AbstractArray}
  genomes::SizedVector{N,GenomeType}
  fitnesses::SizedVector{N,Float64}

  options::Options

  generation::Int

  best_solution_idx::Int
  n_better_than_parents::Int

  _initialized::Bool

  function State{N,GenomeType}(opts::Options) where {N,GenomeType<:AbstractArray}
    s = new{N,GenomeType}()
    s.options = opts
    s.generation = 0
    s.best_solution_idx = -1
    s.n_better_than_parents = 0
    s._initialized = false
    s.fitnesses = SizedVector{N,Float64}(fill(Inf, N))
    s
  end

  function State{N}(genomes::SizedVector{N,GenomeType}, fitnesses::SizedVector{N,Float64}, opts::Options, inited::Bool) where {N,GenomeType}
    new{N,GenomeType}(genomes, fitnesses, opts, 0, -1, 0, inited)
  end

end

@inline function State{N}(genomes::GS, fitnesses, opts::Options, inited=true) where {N,GT<:AbstractArray,GS<:SizedVector{N,GT}}
  State{N,GT}(genomes, fitnesses, opts, -1, 0, 0, inited)
end

@inline function State{N}(genomes::GS, opts::Options) where {N,GT<:AbstractArray,GS<:SizedVector{N,GT}}
  State{N}(genomes, opts, false)
end
#= 
@inline function Base.hash(a::State{N}, h::UInt) where {N}
  hash(Symbol(:State, N), h) |>
  @>(hash(a.genomes)) |>
  @>(hash(a.fitnesses)) |>
  @>(hash(a.options)) |>
  @>(hash(a.generation)) |>
  @>(hash(a.best_solution_idx)) |>
  @>(hash(a.n_better_than_parents)) |>
  @>(hash(a._initialized))
end

@inline function Base.:(==)(a::State{N}, b::State{N}) where {N}
  isequal(a.genomes, b.genomes) &&
    isequal(a.fitnesses, b.fitnesses) &&
    isequal(a.options, b.options) &&
    isequal(a.generation, b.generation) &&
    isequal(a.best_solution_idx, b.best_solution_idx) &&
    isequal(a.n_better_than_parents, b.n_better_than_parents) &&
    isequal(a._initialized, b._initialized)
end

@inline Base.:(==)(::State{N1}, ::State{N2}) where {N1,N2} = false

 =#
@inline fitnesses(s::State) = s.fitnesses
@inline genomes(s::State) = s.genomes

# TODO: equality + hash State:lle

const _StructVecIndiv = StructVector{Individual}

#=
  genomes::SizedVector{N,GenomeType} # genomit
  fitnesses::SizedVector{N,Float64}
=#
(individuals(genomes::AbstractArray{GenomeType}, fitnesses::AbstractArray{Float64})::AbstractArray{Individual}) where {GenomeType} =
  _StructVecIndiv((genomes, fitnesses))
individuals(s::State{N}) where {N} = individuals(s.genomes, s.fitnesses)
individuals_lazy(s::State{N}) where {N} = individuals(s) |> LazyRows
individuals_lazy(genomes::AbstractArray{GenomeType}, fitnesses::AbstractArray{Float64}) where {GenomeType} =
  individuals(genomes, fitnesses) |> LazyRows

function _generate_random_population!(opts::Options, pop::_SizedTypes{N,GT}, including::AbstractArray{GT}=GT[]) where {N,GT<:AbstractArray}
  including_len = length(including)
  @assert including_len ≤ N
  copyto!(pop, including)
  let left_to_generate = N - including_len
    if left_to_generate > 0
      for i in including_len+1:N
        @inbounds pop[i] = generate_random_individual(opts, GT)
      end
    end
  end
  pop
end

function _generate_random_population!(s::State{N,GT}, including::AbstractArray{GT}=GT[]) where {N,GT<:AbstractArray}
  pop = SizedVector{N,GT}(Vector{GT}(undef, N))
  s.genomes = _generate_random_population!(s.options, pop, including)
  s
end

@inline function generate_random_individual(o::Options, ::Type{Vector{Bool}})
  rng = _get_rng(o)
  rand(rng, Bool, rand(rng, o.initial_genome_min_len:o.genome_max_len))
end

function _init!(s::State)
  @assert !s._initialized "GA.State already initialized"
  s._initialized = true
  s |>
  _generate_random_population! |>
  _evaluate_fitnesses! # TODO: sortin pitäis tapahtua tässä kohdin
end

"""
HUOM: mutatoi `fitnesses`iä
"""
function _evaluate_fitnesses!(opts::Options, genomes::_SizedTypes{N,GenomeType}, fitnesses::_SizedTypes{N,Float64}) where {N,GenomeType}
  # TODO: mieti tää evaluointikuvio
  obj_fn = opts.objective_fn

  genome_decoder = @<(decode_genome(opts.codon_size, opts.redundant_per_codon))

  Folds.foreach(individuals_lazy(genomes, fitnesses)) do indiv
    decoded = indiv.genome |> genome_decoder
    # @info decoded |> collect
    # TODO: pitääköhän noi uudet fitnessit palauttaa jotenkin eikä setata suoriltaan? Eeeiii välttis? Tarviiko niitä?
    indiv.fitness = decoded |> obj_fn
  end
  fitnesses
end

function _sort_by_fitness!(s::State{N}) where {N}
  sorted_mask = sortperm(s.fitnesses)
  s.fitnesses = @inbounds s.fitnesses[sorted_mask]
  s.genomes = @inbounds s.genomes[sorted_mask]
  s
end

function _evaluate_fitnesses!(s::State{N}) where {N}
  _evaluate_fitnesses!(s.options, s.genomes, s.fitnesses)
  _sort_by_fitness!(s)
  #=   Folds.map(individuals_lazy(s)) do indiv
      indiv.fitness = s.options.objective_fn(indiv.genome)
    end =#
  s
end

"""
Run one generation. Threaded
"""
function _run_generation!(s::State{N}) where {N}
  # TODO: heitä vittuun kunhan koodi alkaa härmistyä
  @assert s._initialized "State not initialized???"

  # select parents
  # run crossover. HOX: tätä varten pitää tehdä genome -> codons
  # run mutation. HOX: ja sit tänne taas heti codons -> genome
  # evaluate offsprings. HOX: ja tätä varten sit genome -> underlying representation -mäppäys. Ks. genome.jl
  # laske n_better_than_parents
  # environmental selection: joko generational replacement tai elitist
  #   - gen rep: koko populaatio korvataan offspringeillä
  #   - elitist: toinen vanhempi korvataan vaan jos offspring parempi
  # päivitä best_solution_idx 
end

# TODO
function optimize() end

@testitem "GA State" begin
  using Random
  const N = 400
  rng() = Xoshiro(666)
  function obj_fn(genome) 
    _sum = (genome |> Iterators.flatten |> sum)
    (42 - _sum)^2
  end
  opts() = GA.Options(objective_fn=obj_fn, genome_max_len=32, initial_genome_min_len=8, rng=rng())

  s = GA.State{N,Vector{Bool}}(opts()) |> GA._init!
  @test issorted(GA.fitnesses(s))

  let (m, M) = extrema(GA.fitnesses(s))
    @test m != M 
  end

  # samalla rng:llä initialisoidut 2 eri statea pitäis olla samat
  @test GA.State{N,Vector{Bool}}(opts()) |> GA._init! == GA.State{N,Vector{Bool}}(opts()) |> GA._init!

  @test GA.State{N,Vector{Bool}}(opts()) |> GA._init! != GA.State{50,Vector{Bool}}(opts()) |> GA._init!
  # using StaticArrays

  # genome1 = Bool[1, 1, 1, 1]
  # fitness1 = 1.0
  # genome2 = Bool[0, 1]
  # fitness2 = 2.0

  # obj_fn(genome) = 0.0

  # opts = GA.Options(objective_fn=obj_fn)

  #=
   Musica.GA._Individual2[Musica.GA._Individual2(Bool[1, 1, 1, 1], 1.0), Musica.GA._Individual2(Bool[0, 1], 2.0)] == 
   Musica.GA._Individual2[Musica.GA._Individual2(Bool[1, 1, 1, 1], 1.0), Musica.GA._Individual2(Bool[0, 1], 2.0)]


  =#

  # TODO testit

  # pop = SizedVector{2}(genome1, genome2)
  # fits = SizedVector{2}(fitness1, fitness2)
  # s = GA.State{2}(pop, fits, opts)
  # @test GA.individuals(s) == [GA.Individual(genome1, fitness1), GA.Individual(genome2, fitness2)]

end
