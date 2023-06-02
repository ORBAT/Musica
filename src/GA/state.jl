
using StaticArrays, StructArrays, TestItems, Folds
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
  @assert isequal(indiv.fitness, Inf) "Evaluating individual that already has a fitness value"
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
  genome_max_len::Int = 1366

  genome_min_len::Int = 43

  objective_fn::Function
end

Options = _Options

mutable struct _State6{N,GenomeType<:AbstractArray}
  population::SizedVector{N,GenomeType} # genomit
  fitnesses::SizedVector{N,Float64}

  options::Options

  generation::Int

  best_solution_idx::Int
  n_better_than_parents::Int

  _initialized::Bool
end

State = _State6

@inline function State{N}(population::PT, fitnesses, opts::Options, inited=true) where {N,GT<:AbstractArray,PT<:SizedVector{N,GT}}
  State{N,GT}(population, fitnesses, opts, -1, 0, 0, inited)
end

@inline function State{N}(population::PT, opts::Options) where {N,GT<:AbstractArray,PT<:SizedVector{N,GT}}
  State{N}(population, SizedVector{N}(fill(Inf, N)), opts, false)
end

const _StructVecIndiv = StructVector{Individual}

@inline individuals(s::State{N}) where {N} = _StructVecIndiv((s.population, s.fitnesses))
@inline individuals_lazy(s::State{N}) where {N} = individuals(s) |> LazyRows

function _init!(s::State{N}) where {N}
  # TODO: jos ei inited, niin evaluoi fitnessit

end

"""
Run one generation. Threaded
"""
function _run_generation!(s::State{N}) where {N}
  # HOX: toimii vaan jos s._initialized!
  # TODO: heitä vittuun kunhan koodi alkaa härmistyä
  @assert s._initialized "State not initialized???"

  # select parents
  # run crossover
  # run mutation
  # evaluate offsprings. HOX: ennen tätä pitää tehdä genome -> underlying representation -mäppäys. Ks. genome.jl
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

  pop = SizedVector{2}(genome1, genome2)
  fits = SizedVector{2}(fitness1, fitness2)
  s = GA.State{2}(pop, fits, opts)
  @test GA.individuals(s) == [GA.Individual(genome1, fitness1), GA.Individual(genome2, fitness2)]

end
