
using StaticArrays, StructArrays, TestItems, Folds, Random
using ..Musica: _SizedTypes


const Maybe{T} = Union{T, Nothing}

#= ################### NOTE muistiinpanoja

HOX: POPULAATIOSSA VOI OLLA ERI PITUSIA GENOMEJA!!!! Eli populaatio ei voi olla vaan m × N matriisi
Ja pelkästään jo ton takia Metaheuristics ei kyl enää kanna. 
=#

mutable struct Individual{GenomeType<:AbstractArray}
  genome::GenomeType
  fitness::Float64
end

@inline fitness(indiv::Individual) = indiv.fitness
@inline function set_fitness(indiv::Individual, f::Float64)
  indiv.fitness = f
  indiv
end

function _eval_indiv_fitness!(indiv, obj_fn::Function, genome_mapper::Function)
  # TODO KYS: vähän kluge, tiiä ees onko tarpeen. Heitä vittuun jahka homma etenee?
  # @assert isequal(indiv.fitness, Inf) "Evaluating individual that already has a fitness value"
  set_fitness(indiv, obj_fn(genome_mapper(indiv.genome)))
end

# HOX: jostain syystä koko paska kippaa jos Individual:illa tekee tän nimitempun.
# UndefVarError: `Individual` not defined
# Individual = _Individual2

@inline function Base.hash(a::Individual, h::UInt)
  hash(:Individual, h) |> @>(hash(a.genome)) |> @>(hash(a.fitness))
end

@inline function Base.:(==)(a::Individual, b::Individual)
  isequal(a.fitness, b.fitness) && isequal(a.genome, b.genome)
end

Base.@kwdef struct _Options
  # kova raja genomin pituudelle
  genome_max_len::Int = 2048

  initial_genome_min_len::Int = 256
  objective_fn::Function
  rng::Maybe{Random.AbstractRNG} = nothing
end

Options = _Options

function _get_rng(o::Options)
  if isnothing(o.rng)
    Random.default_rng()
  else
    o.rng
  end
end

mutable struct State{N,GenomeType<:AbstractArray}
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

function _init!(s::State{N}) where {N}
  @assert !s._initialized "GA.State already initialized"
  s = s |>
      _generate_random_population! |>
      _evaluate_fitnesses! # TODO: sortin pitäis tapahtua tässä kohdin
end

"""
HUOM: mutatoi `fitnesses`iä
"""
function _evaluate_fitnesses!(opts::Options, genomes::_SizedTypes{N,GenomeType}, fitnesses::_SizedTypes{N,Float64}) where {N,GenomeType}
  # TODO: mieti tää evaluointikuvio
  obj_fn = opts.objective_fn
  Folds.foreach(individuals_lazy(genomes, fitnesses)) do indiv
    # TODO: pitääköhän noi uudet fitnessit palauttaa jotenkin eikä setata suoriltaan? Eeeiii välttis? Tarviiko niitä?
    indiv.fitness = obj_fn(indiv.genome)
  end
  fitnesses
end

function _sort_by_fitness!(s::State{N}) where N 
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
  rng() = Xoshiro(666)
  obj_fn(genome) = sum(genome)
  opts() = GA.Options(objective_fn=obj_fn, genome_max_len=16, initial_genome_min_len=8, rng=rng())
  
  s = GA.State{5,Vector{Bool}}(opts()) |> GA._init!
  s2 = GA.State{5,Vector{Bool}}(opts()) |> GA._init!
  @test issorted(GA.fitnesses(s))

  # TODO FIXME: parempi equality test
  @test s |> GA.genomes == s2 |> GA.genomes && s |> GA.fitnesses == s2 |> GA.fitnesses
  @test GA.genomes(s)[1] == Bool[1, 1, 0, 0, 0, 0, 0, 0]
  @test GA.fitnesses(s)[1] == 2
  @test GA.fitnesses(s)[1] ≤ GA.fitnesses(s)[2]
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
