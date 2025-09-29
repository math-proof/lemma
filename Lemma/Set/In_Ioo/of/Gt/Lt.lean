import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x > a)
  (h₁ : x < b) :
-- imply
  x ∈ Ioo a b := by
-- proof
  constructor
  assumption
  assumption


-- created on 2025-03-30
