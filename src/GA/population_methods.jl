using StatsBase, Random, StructArrays
using ..Musica: SizedType

"""
palauttaa 
    [(parent_a1, parent_b1), (parent_a2, parent_b2), [...], (parent_an, parent_bn)]
"""
@propagate_inbounds function select_parents(population::AbstractArray{Indiv}, n; tournament_size=2, rng=Random.default_rng())::AbstractArray{NTuple{2,Indiv}} where {Indiv}
  # HOX: population pitää olla fitnessin mukaan järjestyksessä, paras eka
  # TODO FIXME: poista tää assert jahka homma pelittää
  @assert issorted(population; by=fitness)
  # (Indiv, Indiv)[]
  parents = Array{NTuple{2,Indiv}}(undef, n)
  for i in 1:n
    @inbounds parents[i] = tournament_select_two(population; tournament_size, rng)
  end
  parents
end

function _tournament_select_with_one_tournament(individuals::AbstractArray{T}, ::Type{Val{n}}; tournament_size, rng)::NTuple{n,T} where {T,n}
  # arvotaan `tournament_size` kpl indeksejä `individuals`ista. Ei toistoja, ja järjestyksessä pienin ensin
  idxs = StatsBase.sample(rng, 1:length(individuals), tournament_size; replace=false, ordered=true)
  # otetaan näistä indekseistä ekat n (eli parhaat `n` kpl), ja käytetään sitä maskina `individuals`ille --> turnauksen parhaat `n` kpl yksilöä
  @inbounds Tuple(individuals[idxs[1:n]])
end

@propagate_inbounds function tournament_select_two(individuals::AbstractArray{T}; tournament_size, rng)::NTuple{2,T} where {T}
  n_indivs = length(individuals)
  parent_a_idx = _tournament_select_idx(n_indivs, tournament_size, rng)
  parent_b_idx = _tournament_select_idx(n_indivs, tournament_size, rng)
  while (parent_a_idx == parent_b_idx)
    parent_b_idx = _tournament_select_idx(n_indivs, tournament_size, rng)
  end
  # HOX: palauttaa fitness-järjestyksessä, paras ensin
  individuals[min(parent_a_idx, parent_b_idx)], individuals[max(parent_a_idx, parent_b_idx)]
end

# function tournament_select(individuals::AbstractArray{T}, ::Type{Val{1}}; tournament_size, rng)::T where {T}
#   # arvotaan `tournament_size` kpl indeksejä `individuals`ista. Ei toistoja, ja järjestyksessä pienin ensin
#   idxs = StatsBase.sample(rng, 1:length(individuals), tournament_size; replace=false, ordered=true)
#   # otetaan näistä indekseistä eka eli paras, käytetään maskina `individuals`ille --> turnauksen paras yksilö
#   @inbounds individuals[idxs[1]]
# end

function _tournament_select_idx(max_idx, tournament_size, rng)
  idxs = StatsBase.sample(rng, 1:max_idx, tournament_size; replace=false, ordered=true)
  @inbounds idxs[1]
end


### HOX HOX HOX HOX:
# eiks tää vittu riko nyt ton mun hienon genomi-idean? Tää saattaa katkasta kodonin näppärästi 
# keskeltä
# HOX HOX HOX HOX HOX
#
## -------> HUOM: ei haittaa! Tää on täysin agnostic a:n ja b:n rakenteelle. et jos niistä tekee esim Vector{Vector{Bool}} tmv ni homma
# pelannee mainiosti. TODO: VITTU TESTAA ETTÄ SE PELAA



# TODO: "virallisesti" crossoverin pitäis palauttaa tietty kaks childiä
function uniform_crossover(a::AbstractArray, b::AbstractArray; rng=Random.default_rng())
  # HOX! vanhemmalta saatujen bittien etäisyydet ei sais muuttua, koska epistaasi (ks essentials of metaheuristics p38). 
  # Se ratkaiseva "geenipatterni" voi olla 
  #     _ _ 1 _ 0 0 1 _ 0
  # tmv, eli bittien keskinäinen välimatka merkitsee.
  # 
  # eli esim jos a:sta otetaan bitit indekseillä [2, 3, 4, 6], ne on sit jälkeläisessä aina just tossa järjestyksessä, ja esim bitin 4 ja 6 välissä 
  # voi olla vaan 1 bitti b:stä

  # a = [10,  20,  30,  40,  50,  60, 70, 80, 90]
  # b = [100, 200, 300, 400, 500]
  a_len = length(a)
  # a_len = 9
  b_len = length(b)
  # b_len = 5

  (shorter, shorter_len, longer, longer_len) = if a_len < b_len
    (a, a_len, b, b_len)
  else
    (b, b_len, a, a_len)
  end
  # shorter = b, longer = a

  # molemmat vanhemmat antaa puolet omasta genomistaan jälkeläiselle
  # HUOM: kun toisen roundaa ylös ja toisen alas, niin jos a_len==b_len ja pariton, ni offspring_len == a_len == b_len
  n_bits_from_shorter = div(shorter_len, 2, RoundUp)
  # n_bits_from_shorter = 3
  n_bits_from_longer = div(longer_len, 2, RoundDown)
  # n_bits_from_longer = 4

  offspring_len = n_bits_from_shorter + n_bits_from_longer
  # offspring_len = 7

  # indeksit, jotka lyhyemmästä tulee mukaan jälkeläiseen
  shorter_mask = StatsBase.sample(rng, 1:shorter_len, n_bits_from_shorter; replace=false, ordered=true)
  # shorter_mask = [1, 3, 5]
  # tää on ikään kuin sapluuna [1, _, 3, _, 5]
  #
  # [100, 200, 300, 400, 500]
  #   ^         ^         ^
  #
  # shorterin sapluuna on yhteensä 5 pitkä (kun laskee "tyhjät välit" mukaan), eli se mahtuu alkamaan jälkeläisessä indekseiltä
  # 1: [s, _, s, _, s, _, _]
  # 2: [_, s, _, s, _, s, _]
  # 3: [_, _, s, _, s, _, s]

  # Arvotaan shorterin sapluunalle satunnainen alkukohta tolle välille, ja "shiftataan" sen indeksit tän alkukohdan mukaisesti.
  # Nää on sit ne _jälkeläisen_ bitti-indeksit jotka tulee shorterilta. Järjestys ja numeroiden suhteellinen paikka säilyy, 
  # shorter_mask vaan siirtyy
  offspring_idxs_from_shorter = _randomize_mask_position(shorter_mask, offspring_len, rng)
  # _randomize_mask_position arpoi alkuindeksiksi 3:n, lopputulos on:
  # offspring_idxs_from_shorter = [3, 5, 7]

  # Me tiedetään että ne bitit jotka ei tullu shorterilta, tulee pakostakin sit longerilta.
  # Tää on offspring_idxs_from_shorter:in komplementti, eli siis _jälkeläisen_ indeksit jotka tulee longerilta. 
  # Ottaa rangesta 1:offspring_len kaikki, jotka ei löydy offspring_idxs_from_shorter:ista.
  offspring_idxs_from_longer = findall((!in).(1:offspring_len, (offspring_idxs_from_shorter,)))
  # offspring_idxs_from_longer = [1, 2, 4, 6]
  #= NOTE:
    When broadcasting with in.(items, collection) or items .∈ collection, both item and collection are broadcasted over, which is often not what is intended. For example, if both arguments are vectors (and the dimensions match), the result is a vector indicating whether each value in collection items is in the value at the corresponding position in collection. To get a vector indicating whether each value in items is in collection, wrap collection in a tuple or a Ref like this: in.(items, Ref(collection)) or items .∈ Ref(collection).
  =#

  # ja tehdään offspring_idxs_from_longer:ista maski longerille (tässä mennään `offspring` idxs -> `longer` idxs, shorterin kanssa mentiin `shorter` idxs -> `offspring` idxs)
  longer_mask = _randomize_mask_position(offspring_idxs_from_longer, longer_len, rng)
  offspring = similar(shorter, offspring_len)
  offspring[offspring_idxs_from_shorter] = shorter[shorter_mask]
  offspring[offspring_idxs_from_longer] = longer[longer_mask]
  offspring
end

"""
HOX: olettaa että `indices` on little-endian järjestyksessä
"""
Base.@propagate_inbounds _mask_len(indices) = (indices[end] - indices[1]) + 1

"""
Indeksi-`mask` shiftattuna satunnaisesti välille `1:max_index`, eli jokaiseen sen elementtiin lisätään joku offset
"""
Base.@propagate_inbounds function _randomize_mask_position(mask, max_index, rng)
  mask_len = _mask_len(mask)
  start_idx = rand(rng, 1:(max_index-mask_len)+1)
  offset = start_idx - mask[1]
  mask .+ offset
end

#= abstract type AbstractMutation end
struct PointMutation <: AbstractMutation end
struct InsertMutation <: AbstractMutation end
struct DeleteMutation <: AbstractMutation end

Base.Base.@propagate_inbounds function mutate!(PointMutation, genome::AbstractArray{Bool}, idx; kw...)::Tuple{AbstractArray{Bool},Int}
  genome[idx] = !genome[idx]
  genome, idx + 1
end

Base.Base.@propagate_inbounds function mutate!(InsertMutation, genome::AbstractArray{Bool}, idx;
  genome_max_len, mut_segment_max_len, restkw...)::AbstractArray{Bool}

end

 =#
#= function mutate_point!(genome::AbstractArray{Bool};kw...)::AbstractArray{Bool}
  idx = rand(1:length(genome))
  @inbounds genome[idx] = @inbounds !genome[idx]
  genome
end

function mutate_insert(genome::AbstractArray;mut_segment_max_len,genome_max_len)

end =#


# HOX TODO: mutaatiotyypit
#=
Point mutation (Substitution): This is a change in a single base pair in the DNA sequence. In the context of a genetic algorithm, this would correspond to changing a single element in your array or list.

Insertion: This is when one or more new base pairs are inserted into the DNA sequence. In a genetic algorithm, this would mean adding one or more new elements at a random location in your array or list.

Deletion: This is when one or more base pairs are removed from the DNA sequence. Similarly, in a genetic algorithm, this would involve removing one or more elements from your array or list.

Inversion: In biology, this refers to a segment of DNA that is flipped in orientation relative to the rest of the chromosome. In a genetic algorithm, this could be implemented as reversing a section of your list or array.

Translocation: In a genome, this involves moving a segment of DNA from one location to another, either within the same chromosome or to a different chromosome. For a genetic algorithm, you could implement this as moving a segment of your array or list from one location to another.

Duplication (or amplification): This refers to a piece of DNA that is copied one or more times. In the context of a genetic algorithm, this could be implemented as duplicating a segment of your list or array.

=#

Base.@kwdef struct MutationOptions
  mut_segment_mean_len::Int = default_genome_codon_length # mean segment length in mutations
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

end