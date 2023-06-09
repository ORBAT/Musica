using StatsBase, Random, StructArrays
using ..Musica: _SizedTypes

"""
palauttaa 
    [(parent_a1, parent_b1), (parent_a2, parent_b2), [...], (parent_an, parent_bn)]
"""
function select_parents(population::AbstractArray{Indiv}, n; tournament_size=2, rng=Random.default_rng())::AbstractArray{NTuple{2,Indiv}} where {Indiv}
  # HOX: population pitää olla fitnessin mukaan järjestyksessä, paras eka
  # TODO FIXME: poista tää assert jahka homma pelittää
  @assert issorted(population; by=fitness)
  # (Indiv, Indiv)[]
  parents = Array{NTuple{2,Indiv}}(undef, n)
  foreach(1:n) do i
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

function tournament_select_two(individuals::AbstractArray{T}; tournament_size, rng)::NTuple{2,T} where {T}
  parent_a_idx = _tournament_select_idx(individuals; tournament_size, rng)
  parent_b_idx = _tournament_select_idx(individuals; tournament_size, rng)
  while (parent_a_idx == parent_b_idx)
    parent_b_idx = _tournament_select_idx(individuals; tournament_size, rng)
  end
  @inbounds individuals[min(parent_a_idx, parent_b_idx)], individuals[max(parent_a_idx, parent_b_idx)]
end

# function tournament_select(individuals::AbstractArray{T}, ::Type{Val{1}}; tournament_size, rng)::T where {T}
#   # arvotaan `tournament_size` kpl indeksejä `individuals`ista. Ei toistoja, ja järjestyksessä pienin ensin
#   idxs = StatsBase.sample(rng, 1:length(individuals), tournament_size; replace=false, ordered=true)
#   # otetaan näistä indekseistä eka eli paras, käytetään maskina `individuals`ille --> turnauksen paras yksilö
#   @inbounds individuals[idxs[1]]
# end

function _tournament_select_idx(individuals::AbstractArray{T}; tournament_size, rng) where {T}
  idxs = StatsBase.sample(rng, 1:length(individuals), tournament_size; replace=false, ordered=true)
  @inbounds idxs[1]
end


### HOX HOX HOX HOX:
# eiks tää vittu riko nyt ton mun hienon genomi-idean? Tää saattaa katkasta kodonin näppärästi 
# keskeltä
# HOX HOX HOX HOX HOX
#
## -------> HUOM: ei haittaa! Tää on täysin agnostic a:n ja b:n rakenteelle. et jos niistä tekee esim Vector{Vector{Bool}} tmv ni homma
# pelannee mainiosti. TODO: VITTU TESTAA ETTÄ SE PELAA




function uniform_crossover(a::AbstractArray, b::AbstractArray; rng=Random.default_rng())
  # FIXME: kommenttien yksityiskohdat on vähän vituillaan ku muokkasin lennossa, vois fiksaa

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

  # kun toisen roundaa ylös ja toisen alas, niin jos a_len==b_len ja pariton, ni offspring_len == a_len == b_len
  n_bits_from_shorter = div(shorter_len, 2, RoundUp)
  # n_bits_from_shorter = 3
  n_bits_from_longer = div(longer_len, 2, RoundDown)
  # n_bits_from_longer = 4
  offspring_len = n_bits_from_shorter + n_bits_from_longer
  # offspring_len = 8

  # indeksit, jotka lyhyemmästä tulee mukaan jälkeläiseen
  shorter_mask = StatsBase.sample(rng, 1:shorter_len, n_bits_from_shorter; replace=false, ordered=true)
  # shorter_mask = [1, 3, 5]
  # tää on ikään kuin sapluuna [1, _, 3, _, 5]
  #
  # [100, 200, 300, 400, 500]
  #   ^         ^         ^
  #
  # shorterin sapluuna on yhteensä 5 pitkä (kun laskee "tyhjät välit" mukaan), eli se mahtuu alkamaan jälkeläisessä indekseiltä
  # 1: [s, _, s, _, s, _, _, _]
  # 2: [_, s, _, s, _, s, _, _]
  # 3: [_, _, s, _, s, _, s, _]
  # 4: [_, _, _, s, _, s, _, s]
  # start_idx = rand(1:(offspring_len-shorter_mask_len)+1)
  # start_idx = rand(1:(8-5)+1)
  # start_idx = 3

  # nyt sitä sapluunaa pitää shiftata sen verran että se alkaa halutusta kohdasta.
  #
  # Nää on sit ne _jälkeläisen_ bitti-indeksit jotka tulee shorterilta. Järjestys ja numeroiden suhteellinen paikka säilyy, 
  # shorter_mask vaan siirtyy
  # idxs_from_shorter = shorter_mask .+ shorter_mask_offset
  idxs_from_shorter = _randomize_mask_position(shorter_mask, offspring_len, rng)
  # idxs_from_shorter = [3, 5, 7]

  # Me tiedetään että ne bitit jotka ei tullu shorterilta, tulee pakostakin sit longerilta. 
  # idxs_from_shorter:in komplementti, eli siis _jälkeläisen_ indeksit jotka tulee longerilta. Tää ottaa rangesta 1:offspring_len kaikki,
  # jotka ei löydy idxs_from_shorter:ista.
  idxs_from_longer = findall((!in).(1:offspring_len, (idxs_from_shorter,)))
  # idxs_from_longer = [1, 2, 4, 6, 8]
  #= NOTE:
    When broadcasting with in.(items, collection) or items .∈ collection, both item and collection are broadcasted over, which is often not what is intended. For example, if both arguments are vectors (and the dimensions match), the result is a vector indicating whether each value in collection items is in the value at the corresponding position in collection. To get a vector indicating whether each value in items is in collection, wrap collection in a tuple or a Ref like this: in.(items, Ref(collection)) or items .∈ Ref(collection).
  =#

  # ja tehdään idxs_from_longer:ista maski longerille (nyt mentiin `offspring` idxs -> `longer` idxs, shorterin kanssa mentiin `shorter` idxs -> `offspring` idxs)
  longer_mask = _randomize_mask_position(idxs_from_longer, longer_len, rng)
  offspring = similar(shorter, offspring_len)
  offspring[idxs_from_shorter] = shorter[shorter_mask]
  offspring[idxs_from_longer] = longer[longer_mask]
  offspring
end

"""
HOX: olettaa että `indices` on little-endian järjestyksessä
"""
Base.@propagate_inbounds _mask_len(indices) = (indices[end] - indices[1]) + 1

"""
`mask` shiftattuna satunnaisesti välille `1:max_index`
"""
Base.@propagate_inbounds function _randomize_mask_position(mask, max_index, rng)
  mask_len = _mask_len(mask)
  start_idx = rand(rng, 1:(max_index-mask_len)+1)
  offset = start_idx - mask[1]
  mask .+ offset
end