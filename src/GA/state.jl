
using StaticArrays, StructArrays, TestItems, Folds
using Musica: @©, @£
#= ################### NOTE muistiinpanoja

HOX: POPULAATIOSSA VOI OLLA ERI PITUSIA GENOMEJA!!!! Eli populaatio ei voi olla vaan m × N matriisi
Ja pelkästään jo ton takia Metaheuristics ei kyl enää kanna. 
=#

mutable struct Individual{GenomeType<:AbstractArray}
  genome::GenomeType
  fitness::Float64
end

function evaluate_individual!(indiv, obj_fn::Function)
  indiv.fitness = obj_fn(indiv.genome)
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
  genome_max_len::Int = 1024

  # alotuspopulaation genomien minimikoko
  initial_genome_min_len::Int = 32

  objective_fn::Function
end

Options = _Options

mutable struct _State5{N,GenomeType<:AbstractArray}
  population::SizedVector{N,GenomeType} # genomit
  fitnesses::SizedVector{N,Float64}

  options::Options
  
  generation::Int
  
  """
  Index of best solution so far
  """
  best_idx::Int
  n_better_than_parents::Int
end

State = _State5

@inline function State{N}(population::PT, fitnesses, opts::Options) where {N,GT<:AbstractArray,PT<:SizedVector{N, GT}} 
  State{N,GT}(population, fitnesses, opts, -1, 0, 0)
end

@inline State{N}(population::PT, opts::Options) where {N,GT<:AbstractArray,PT<:SizedVector{N, GT}}  = State{N}(population, SizedVector{N}(zeros(Float64, N)), opts)

@inline individuals(s::State{N}) where {N} = StructVector{Individual}((s.population, s.fitnesses))
@inline individuals_lazy(s::State{N}) where {N} = individuals(s) |> LazyRows

"""
Run one generation / step. Threaded
"""
function trun_generation!(s::State{N}) where {N}
  # select parents
  # run crossover
  # run mutation
  # evaluate offspring. HOX: ennen tätä pitää tehdä genome -> underlying representation -mäppäys. Ks. genome.jl
  # 
end

@testitem "GA State" begin
  using StaticArrays

  genome1 = BitVector((1, 1, 1, 1))
  fitness1 = 1.0
  genome2 = BitVector((0, 1))
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
