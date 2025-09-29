import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : x ≤ b) :
-- imply
  x ∈ Icc a b :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2025-03-01
