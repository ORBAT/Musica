using StatsBase, Random

Base.@propagate_inbounds _mask_len(m) = (m[end] - m[1]) + 1

function uniformish_crossover(a, b; switch_probability=0.5, rng=Random.default_rng())
  # a = [10,  20,  30,  40,  50,  60,  70]
  # b = [100, 200, 300, 400, 500]
  len_a = length(a)
  # len_a = 7
  len_b = length(b)
  # len_b = 5

  n_bits_from_a = div(len_a, 2, RoundUp)
  # n_bits_from_a = 4
  n_bits_from_b = div(len_b, 2, RoundUp)
  # n_bits_from_b = 3
  offspring_len = n_bits_from_a + n_bits_from_b
  # offspring_len = 7
  offspring = similar(a, offspring_len)

  # HOX! vanhemmalta saatujen bittien etäisyydet ei saa muuttua, koska linkage (ks essentials of metaheuristics p38)
  # eli esim jos a:sta otetaan bitit [2, 3, 4, 6], ne on aina just tossa järjestyksessä, ja esim bitin 4 ja 6 välissä 
  # voi olla vaan 1 bitti b:stä

  a_idxs = StatsBase.sample(1:len_a, n_bits_from_a; replace=false, ordered=true)
  # a_idxs = [2, 3, 4, 6]
  # -> [_, 20, 30, 40, 50, 60, _]
  # "a-sapluuna" on yhteensä 5 pitkä ( (a_idxs[end] - a_idxs[1]) + 1 )
  a_mask_len = @inbounds _mask_len(a_idxs)
  # se mahtuu teoriassa alkamaan jälkeläisessä idxiltä:
  # 1: [a, a, a, b, a, b, b]
  # 2: [b, a, a, a, b, a, b]
  # 3: [b, b, a, a, a, b, a]
  # ~~~~~~~eli start_idx voi olla rand(1:(offspring_len-a_mask_len)+1)~~~~~~
  # HOX TODO: tässä pitää ottaa huomioon se, että b:lle jää tilaa
  start_idx = rand(1:(offspring_len-a_mask_len)+1)
  # --> start_idx = 1
  # nyt tätä sapluunaa pitää shiftata sen verran että se alkaa halutusta kohdasta
  a_offset = @inbounds start_idx - a_idxs[1]
  # a_offset = 
  # offspringin näille indekseille tulee a:n bitit
  idxs_from_a = a_idxs .+ a_offset
  # idxs_from_a = [1, 2, 3, 5]

  # a_idxs = [1, 3, 4, 7]
  

  # eli sit kaikki indeksit, joita ei oteta a:sta otetaan b:stä
  idxs_from_b = findall((!in).(1:offspring_len, (idxs_from_a,)))
  # idxs_from_b = [4, 6, 7]
  # HOX HOX mitäs jos tähän oliskin osunu idxs_from_a = [2,3,4,5]
  # millon idxs_from_b olis [1, 6, 7] ja b_mask_len = 7


  #= NOTE:
    When broadcasting with in.(items, collection) or items .∈ collection, both item and collection are broadcasted over, which is often not what is intended. For example, if both arguments are vectors (and the dimensions match), the result is a vector indicating whether each value in collection items is in the value at the corresponding position in collection. To get a vector indicating whether each value in items is in collection, wrap collection in a tuple or a Ref like this: in.(items, Ref(collection)) or items .∈ Ref(collection).
  =#
  # b_mask_len = @inbounds _mask_len()






  # nyt esim: a:n bitit voidaan asetella

  #=
  # (min_len, max_len) = minmax(len_a, len_b)
  (shorter, min_len, longer, max_len) = if len_a > len_b
    (b, len_b, a, len_a)
  else
    (a, len_a, b, len_b)
  end

   offspring_len = if len_a != len_b
    # TODO: oisko tähän jotain fiksumpaa?
    div(len_a, 2) + div(len_b, 2)
  else
    len_a
  end
  bits_per_parent = div(offspring_len, 2)
  offspring = similar(a, offspring_len)
  # bits_from_a = sample(1:len_a, min(len_a, bits_per_parent); replace=false)
  use_whole_short_parent = bits_per_parent ≥ min_len
  idxs_from_shorter = if use_whole_short_parent
    1:min_len
  else
    StatsBase.sample(1:min_len, bits_per_parent;replace=false)
  end

  =#
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



  @inbounds offspring[from_a] = @inbounds a[from_a]
  @inbounds offspring[from_b] = @inbounds b[from_b]

  =#

  offspring
end