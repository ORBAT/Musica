using StatsBase,Random

function uniformish_crossover(a, b; switch_probability=0.5,rng=Random.default_rng())
  len_a = length(a)
  len_b = length(b)
  # (min_len, max_len) = minmax(len_a, len_b)
  (shorter, min_len, longer, max_len) = if len_a > len_b
    (b, len_b, a, len_a)
  else
    (a, len_a, b, len_b)
  end

  offspring_len = if len_a != len_b
    # TODO: oisko tähän jotain fiksumpaa?
    rand(min_len:max_len)
  else
    len_a
  end
  bits_per_parent = div(offspring_len, 2)
  @assert bits_per_parent < min_len ""
  offspring = similar(a, offspring_len)
  # bits_from_a = sample(1:len_a, min(len_a, bits_per_parent); replace=false)
  use_whole_short_parent = bits_per_parent > min_len
  idxs_from_shorter = StatsBase.sample(1:min_len, bits_per_parent;replace=false)
  

#=
  Bool[0, 1, 0, 0, 1, 0, 1]
       a, b, a, a, b, a, b 
=#

  #=
  switch_points = rand(offspring_len) .≥ switch_probability

  jos tekis tän niin, että aina kun switch_points:issa on 1, niin ruvetaan lukemaan toisesta parentista
  Bool[0, 1, 0, 0, 1, 0, 1]
       a, b, b, b, a, a, b 

  eiku tääkin kusee

  HOX: tää allaoleva kusee jos a ja b pituudet on riittävän eri


  # indeksit jotka otetaan a:sta
  from_a = findall(probs .≥ switch_probability)
  # indeksit jotka ei oo from_a:ssa otetaan b:stä
  # FIXME: vähän kluge?
  from_b = findall((!in).(1:offspring_len, (from_a,)))
  #= ?in sanoi että
    When broadcasting with in.(items, collection) or items .∈ collection, both item and collection are broadcasted over, which is often not what is intended. For example, if both arguments are vectors (and the dimensions match), the result is a vector indicating whether each value in collection items is in the value at the corresponding position in collection. To get a vector indicating whether each value in items is in collection, wrap collection in a tuple or a Ref like this: in.(items, Ref(collection)) or items .∈ Ref(collection).
  =#



  @inbounds offspring[from_a] = @inbounds a[from_a]
  @inbounds offspring[from_b] = @inbounds b[from_b]

  =#

  offspring
end