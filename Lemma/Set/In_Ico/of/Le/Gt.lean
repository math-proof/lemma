import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : b > x) :
-- imply
  x ∈ Ico a b := by
-- proof
  aesop


-- created on 2025-08-05
