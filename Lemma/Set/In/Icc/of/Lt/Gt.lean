import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {x a b : α}
-- given
  (h₀ : x < b)
  (h₁ : x > a) :
-- imply
  x ∈ Ioo a b :=
-- proof
  ⟨h₁, h₀⟩


-- created on 2026-09-26
