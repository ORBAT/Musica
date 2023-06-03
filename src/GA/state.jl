
using StaticArrays, StructArrays, TestItems, Folds, Random
using ..Musica: _SizedTypes

#= ################### NOTE muistiinpanoja

HOX: POPULAATIOSSA VOI OLLA ERI PITUSIA GENOMEJA!!!! Eli populaatio ei voi olla vaan m × N matriisi
Ja pelkästään jo ton takia Metaheuristics ei kyl enää kanna. 
=#

mutable struct Individual{GenomeType<:AbstractArray}
  genome::GenomeType
  fitness::Float64
end

function _calc_indiv_fitness!(indiv, obj_fn::Function, genome_mapper::Function)
  # TODO KYS: vähän kluge, tiiä ees onko tarpeen. Heitä vittuun jahka homma etenee?
  # @assert isequal(indiv.fitness, Inf) "Evaluating individual that already has a fitness value"
  indiv.fitness = obj_fn(genome_mapper(indiv.genome))
end

# HOX: jostain syystä koko paska kippaa jos Individual:illa tekee tän nimitempun.
# UndefVarError: `Individual` not defined
# Individual = _Individual2

@inline function Base.hash(a::Individual, h::UInt)
  hash(:Individual, h) |> @©(hash(a.genome)) |> @©(hash(a.fitness))
end

@inline function Base.:(==)(a::Individual, b::Individual)
  isequal(a.fitness, b.fitness) && isequal(a.genome, b.genome)
end

Base.@kwdef struct _Options
  # kova raja genomin pituudelle
  genome_max_len::Int = 2048

  initial_genome_min_len::Int = 256
  objective_fn::Function

  # TODO HOX: rng???
  # -> Random.default_rng() ei oo thread safe (koska se on task local), eli
  # sitä ei voi vaan passailla ympäriinsä jos ei ihan tiiä mihin threadiin se joutuu
end

Options = _Options

mutable struct State{N,GenomeType<:AbstractArray}
  genomes::SizedVector{N,GenomeType} # genomit
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

const _StructVecIndiv = StructVector{Individual}

#=
  genomes::SizedVector{N,GenomeType} # genomit
  fitnesses::SizedVector{N,Float64}
=#
individuals(genomes::AbstractArray{GenomeType}, fitnesses::AbstractArray{Float64}) where {GenomeType} =
  _StructVecIndiv((genomes, fitnesses))
individuals(s::State{N}) where {N} = individuals(s.genomes, s.fitnesses)
individuals_lazy(s::State{N}) where {N} = individuals(s) |> LazyRows
individuals_lazy(genomes::AbstractArray{GenomeType}, fitnesses::AbstractArray{Float64}) where {GenomeType} =
  individuals(genomes, fitnesses)

function _initialize_population!(s::State{N,GT}, including::AbstractArray{GT}=GT[]) where {N,GT<:AbstractArray}
  including_len = length(including)
  @assert including_len ≤ N

  pop = Vector{GT}(undef, N)
  copyto!(pop, including)
  let left_to_generate = N - including_len
    if left_to_generate > 0
      @inbounds for i in including_len+1:N
        pop[i] = generate_random_individual(GT, s.options)
      end
    end
  end

  s.genomes = SizedVector{N}(pop)
  nothing
end

@inline function generate_random_individual(::Type{Vector{Bool}}, o::Options)
  rand(Bool, rand(o.initial_genome_min_len:o.genome_max_len))
end

function _init!(s::State{N}) where {N}
  @assert !s._initialized "GA.State already initialized"
  _initialize_population!(s)
  _evaluate_fitnesses!(s)
end

function _evaluate_fitnesses!(opts::Options, genomes::_SizedTypes{N, GenomeType}, fitnesses::_SizedTypes{N, Float64}) where {N, GenomeType}
  # TODO: mieti tää evaluointikuvio
end

function _evaluate_fitnesses!(s::State{N}) where {N}
  Folds.map(individuals_lazy(s)) do indiv
    # TODO: pitääköhän noi uudet fitnessit palauttaa jotenkin eikä setata suoriltaan
    indiv.fitness = s.options.objective_fn(indiv.genome)
  end
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

@testitem "GA State" begin
  using StaticArrays

  genome1 = Bool[1, 1, 1, 1]
  fitness1 = 1.0
  genome2 = Bool[0, 1]
  fitness2 = 2.0

  obj_fn(genome) = 0.0

  opts = GA.Options(objective_fn=obj_fn)

  #=
   Musica.GA._Individual2[Musica.GA._Individual2(Bool[1, 1, 1, 1], 1.0), Musica.GA._Individual2(Bool[0, 1], 2.0)] == 
   Musica.GA._Individual2[Musica.GA._Individual2(Bool[1, 1, 1, 1], 1.0), Musica.GA._Individual2(Bool[0, 1], 2.0)]


  =#

  # FIXME testit

  # pop = SizedVector{2}(genome1, genome2)
  # fits = SizedVector{2}(fitness1, fitness2)
  # s = GA.State{2}(pop, fits, opts)
  # @test GA.individuals(s) == [GA.Individual(genome1, fitness1), GA.Individual(genome2, fitness2)]

end
