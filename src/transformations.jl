using Transducers, TestItems, Test

  # foldl takes a fn (acc, x). (fn ∘ _left) is (acc,_) -> fn(acc)
  # this is basically just fn composed with itself `times` times (fn ∘ fn ∘ ... )
repeated(fn, times) = (input) -> foldl((fn ∘ _left), 1:times; init=input)

_left(a, _) = a