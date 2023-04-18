using Transducers, TestItems, Test

  # foldl takes a fn (acc, x). (fn ∘ _left) is (acc,_) -> fn(acc)
  # this is basically just fn composed with itself `times` times (fn ∘ fn ∘ ... )
"""
    repeated(fn, times)

Compose `fn` with itself `times` times
"""
function repeated(fn, times) 
  if times ≥ 20
   repeated_fold(fn, times)
  else
    repeated_compose(fn, times)
  end
end

repeated_compose(fn, times) = ∘(fill(fn, times)...)

repeated_fold(fn, times)  = (input) -> foldl((fn ∘ _left), 1:times; init=input)

_left(a, _) = a