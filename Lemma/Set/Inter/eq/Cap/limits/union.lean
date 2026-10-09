import sympy.Basic
import Mathlib


@[path]
private lemma main
  {A B : Set ℤ}
  {f : ℤ → Set α} :
-- imply
  (⋂ k ∈ A, f k) ∩ ⋂ k ∈ B, f k = ⋂ k ∈ A ∪ B, f k := by
-- proof
  rw [Set.biInter_union]


-- created on 2021-04-28
