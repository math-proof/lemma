import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : x ≤ b) :
-- imply
  x ∈ Icc a b :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2026-10-03
