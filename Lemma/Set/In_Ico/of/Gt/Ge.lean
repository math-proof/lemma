import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : b > x)
  (h₁ : x ≥ a) :
-- imply
  x ∈ Ico a b := by
-- proof
  constructor
  assumption
  assumption


-- created on 2025-03-30
