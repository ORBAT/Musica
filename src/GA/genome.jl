using ..Musica
using ..Musica: SizedType
using Transducers, TestItems, Parameters, StaticArrays, Static
using Base: RefValue

const default_genome_codon_length::Int = 6
const default_genome_redundant_per_codon::Int = 2
const default_max_codons::Int = 400

"""
  - `ElemType` on yksittäisen "emäksen" tyyppi. Kun `NStates` == 2 niin defaultti on `Bool`
  - `NStates` kertoo kuinka monta "basea" genomissa on. Binäärikamassa `NStates` == 2. DNA:ssa `NStates` = 4 (A, C, G, T)
  - `CodonLen` on yksittäisen "kodonin" kokonaispituus. Jokaisesta kodonista tiputetaan `NRedundant` viimeistä elementtiä pois

KYS: `ElemType` ei oikein oo järkevän oloinen. Pitäis ehkä olla "flätin" genomin tyyppi?
--> eiköhän se oo jees. Flätti on `<: AbstractArray{ElemType}`, dekoodattu sit melkein mitä vaan
"""
@with_kw struct GenomeOptions{ElemType,CodonLen,NRedundant,NStates}
  max_codons::Int = default_max_codons
  min_codons::Int = 3

  Base.@propagate_inbounds function GenomeOptions{ElemType,CodonLen,NRedundant,NStates}(
    max_codons,
    min_codons,
  ) where {ElemType,CodonLen,NRedundant,NStates}
    @boundscheck @assert NRedundant < CodonLen
    @boundscheck @assert max_codons ≥ min_codons
    new{ElemType,CodonLen,NRedundant,NStates}(max_codons, min_codons)
  end
end

function GenomeOptions{CodonLen,NRedundant}(; restkw...) where {CodonLen,NRedundant}
  GenomeOptions{Bool,CodonLen,NRedundant,2}(; restkw...)
end

"""
NOTE: tää on sitä varten että Parameters.@with_kw:n luomat konstruktorit toimii ilman tyyppiparametreja, eli
GenomeOptions() ja GenomeOptions(max_codons=50)
"""
function GenomeOptions(maxc, minc)
  GenomeOptions{Bool,default_genome_codon_length,default_genome_redundant_per_codon,2}(maxc, minc)
end

@inline genome_max_length(opts::GenomeOptions{NS,CodonLen}) where {NS,CodonLen} =
  CodonLen * opts.max_codons
@inline genome_min_length(opts::GenomeOptions{NS,CodonLen}) where {NS,CodonLen} =
  CodonLen * opts.min_codons

# HOX: hoitaa vaan maksimin
function clamp_genome_length!(opts::GenomeOptions{T,CL,NR}, genome) where {T,CL,NR}
  # FIXME: minimin hanskaus
  let max_len = genome_max_length(opts)
    if length(genome) > max_len
      resize!(genome, max_len)
    end
  end
  genome
end

function genome_length_extrema(go::GenomeOptions{NS,CL}) where {NS,CL}
  genome_min_length(go), genome_max_length(go)
end

@inline active_codon_length(
  ::Type{<:GenomeOptions{T,CodonLen,NRedundant}},
) where {T,CodonLen,NRedundant} = CodonLen - NRedundant

@inline active_codon_length(v::GenomeOptions) = v |> typeof |> active_codon_length

@inline redundant_per_codon(::Type{<:GenomeOptions{T,CL,NR}}) where {T,CL,NR} = NR
@inline redundant_per_codon(v::GenomeOptions) = v |> typeof |> redundant_per_codon

@inline codon_length(::Type{<:GenomeOptions{T,CodonLen}}) where {T,CodonLen} = CodonLen
@inline codon_length(v::GenomeOptions) = v |> typeof |> codon_length

Base.@assume_effects :foldable _nearest_mul_of(near, x) =
  let _rem = x % near
    _rem == 0 ? x : x + (near - _rem)
  end

split_into_codons(opts::GenomeOptions, genome::StaticVector{L}) where {L} =
  split_into_codons(opts, genome, L)

split_into_codons(opts::GenomeOptions, genome) = split_into_codons(opts, genome, length(genome))

split_into_codons(opts::GenomeOptions{T,CodonLen}, genome, L) where {T,CodonLen} =
  genome |> @<(ZeroPadded(_nearest_mul_of(CodonLen, L))) |>
  Consecutive(Val{CodonLen}(), Val{CodonLen}())

function split_into_codons_view(opts::GenomeOptions{T,CodonLen}, genome) where {T,CodonLen}
  padded_len = _nearest_mul_of(CodonLen, length(genome))
  # pad the genome with zeros at the end so its length is a multiple of CodonLen
  padded_genome = genome |> @<(ZeroPadded(padded_len))

  # 1:CodonLen:padded_len |> Map(i -> (SizedVector{CodonLen}(@view padded_genome[i:(i+CodonLen)-1])))

  # Iterators.map(
  #   i -> SizedVector{CodonLen}(@view padded_genome[i:(i+CodonLen)-1]),
  #   1:CodonLen:padded_len,
  # )
  # NOTE: this is literally the same as doing Iterators.map(i -> SizedVector{CodonLen}(@view ...))
  (SizedVector{CodonLen}(@view padded_genome[i:(i+CodonLen)-1]) for i in 1:CodonLen:padded_len)
end

without_redundant_codons(opts::GenomeOptions{T,CL,NR}, codons) where {T,CL,NR} =
  codons |> Map(x -> droplast(x, static(NR)))
# HOX: pelkän Map(@<(droplast(NR))) käyttö tässä aiheuttaa type instabilityä, koska constant propagation menee särki ja NR päätyy tavallisena inttinä BoundCall.arg:iin. Kääriminen static():iin auttaa siihen, koska sit arg on StaticInt
# HOX: MUTTA MUTTA MUTTA, BoundCall on jostain syystä vitun hidas, pelkkä without_redundant_codons kutsu kestää 950ns vs 1.5ns (siis ilman collectia)

@testitem "genome mappings" begin
  using StaticArrays
  let opts = GA.GenomeOptions{6,2}()
    @test GA.split_into_codons_view(opts, 1:15) |> collect == [
      [1, 2, 3, 4, 5, 6],
      [7, 8, 9, 10, 11, 12],
      [13, 14, 15, 0, 0, 0],
    ]

    @test GA.split_into_codons(opts, 1:15) |> collect == [
      (1, 2, 3, 4, 5, 6),
      (7, 8, 9, 10, 11, 12),
      (13, 14, 15, 0, 0, 0),
    ]

    @test GA.split_into_codons_view(opts, SVector{15}(1:15)) |>
          @>(GA.without_redundant_codons(opts)) |>
          collect == [
      [1, 2, 3, 4],
      [7, 8, 9, 10],
      [13, 14, 15, 0],
    ]

    # nää on kaikki keskenään samoja, koska 1:17 ja 1:18 lisää vaan 1 tai 2 redundanttia kodonia, eli niitä ei tuu dekoodattuun outputtiin yhtään.
    @test GA.split_into_codons(opts, SVector{16}(1:16)) |> @>(GA.without_redundant_codons(opts)) |>
          collect ==
          GA.split_into_codons(opts, SVector{17}(1:17)) |> @>(GA.without_redundant_codons(opts)) |>
          collect ==
          GA.split_into_codons(opts, SVector{18}(1:18)) |> @>(GA.without_redundant_codons(opts)) |>
          collect
    # ja sama viewejä käytettäessä
    @test GA.split_into_codons_view(opts, SVector{16}(1:16)) |>
          @>(GA.without_redundant_codons(opts)) |>
          collect ==
          GA.split_into_codons_view(opts, SVector{17}(1:17)) |>
          @>(GA.without_redundant_codons(opts)) |>
          collect ==
          GA.split_into_codons_view(opts, SVector{18}(1:18)) |>
          @>(GA.without_redundant_codons(opts)) |>
          collect
  end
  let genome = SVector{14}(1.0:14.0), opts = GA.GenomeOptions{Float64,4,1,2}()
    @test GA.split_into_codons_view(opts, genome) |> collect == [
      [1.0, 2.0, 3.0, 4.0],
      [5.0, 6.0, 7.0, 8.0],
      [9.0, 10.0, 11.0, 12.0],
      [13.0, 14.0, 0.0, 0.0],
    ]
  end
end

# TODO: `Codon`in tyyppi vois ny alkuun olla SizedVector koska `split_into_codons_view`, mutta tarvinnee mietintää
const Codon{CodonLen,Elem} = SizedVector{CodonLen,Elem}
const CodonSeq{CodonLen,Elem} = Vector{Codon{CodonLen,Elem}}
# TODO: `TranscriptionFactor`in tyyppi
const TranscriptionFactor{Elem} = Vector{Elem}

struct Token{CodonLen,Elem}
  toktype::Symbol
  codons::CodonSeq{CodonLen,Elem}
end

"""
    AbstractGeneticElem{CodonLen,Elem}

Abstract type for elements of a genome.
"""
abstract type AbstractGeneticElem{CodonLen,Elem} end

# TODO: mitenhän noi alku- ja loppusekvenssit oikein kandeis hoitaa. Vähän raskaan olonen tää erillinen tyyppi
struct Delimiters{T}
  start::T
  stop::T
end

# TODO
to_codons(ge::AbstractGeneticElem) = @WIP
# hasproperty(ge, :codons) ?
# ge.codons :
# throw(ArgumentError("to_codons not defined for ", ge |> typeof))

"""
    NonCodingRegion{CodonLen,E}

A sequence of codons that isn't transcribed to anything.
"""
struct NonCodingRegion{CL,E} <: AbstractGeneticElem{CL,E}
  codons::CodonSeq{CL,E}
end

struct RegulatorySeq{CL,E} <: AbstractGeneticElem{CL,E}
  stop::Codon{CL,E}
  codons::CodonSeq{CL,E}

  bound_transcription_factors::Vector{TranscriptionFactor{E}}
end

# TODO
struct Intron{CL,E} <: AbstractGeneticElem{CL,E}
  # delims::Delimiters{Codon{CL,E}}
  codons::CodonSeq{CL,E}
end

# TODO
struct Exon{CL,E} <: AbstractGeneticElem{CL,E}
  codons::CodonSeq{CL,E}
end

struct Gene{CL,E} <: AbstractGeneticElem{CL,E}
  # delims::Delimiters{Codon{CL,E}}
  codons::CodonSeq{CL,E}

  # TODO: intron / exon mechanism
  # coding_region::RefValue{CodonSeq{CL,E}} # ORF without introns
  # HUOM: tähän vaikuttaa operonin promoter-`RegulatorySeq` ja siihen bindautuneet `TranscriptionFactor`it. Vois ehkä olla välillä [-1,1], ja pitää olla yli jonkun kynnyksen (tyyliin yli 0?) että geeni ekspressoituu.
  expression_level::RefValue{Float64}
  transcription_factor::RefValue{TranscriptionFactor{E}}
end

struct Operon{CL,E} <: AbstractGeneticElem{CL,E}
  delims::Delimiters{CodonSeq{CL,E}}
  # promoter/operator/enhancer/silencer in one
  promoter::RegulatorySeq{CL,E}

  terminator_seq::CodonSeq{CL,E}
  # contents::

  # codons            :: Cs # decoded into 0+ `Gene`s
  # _decoded_genes::RefValue{Gs} # memoized decoded Genes

  # QUE: where do I put RegulatorySeqs that are acting on the operon?
end

# Cell sisältää koko genomin (ei siis vaan Cellin "consensus sequence" transkriboidessa valmiina oleva genomi, vaan koko paska), ja kun se translatoidaan se käyttäytyy niin ku kaikkiin genomin operoneiden promotereihin olis bindautunu jotkut tietyt proteiinit
# HOX: miten estää ikuinen rekursio? Cell sisältää sen operonin joka sen loi
struct Cell{CL,E}
  # HUOM: Cellin jokainen Operon käyttäytyy ku sen promoteriin olis bindautunu with_protein
  with_protein::TranscriptionFactor{E}
  genome::Vector{Operon{CL,E}}
end