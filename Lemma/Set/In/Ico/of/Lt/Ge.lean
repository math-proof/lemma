import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {x a b : α}
-- given
  (h₀ : x < b)
  (h₁ : x ≥ a) :
-- imply
  x ∈ Ico a b :=
-- proof
  ⟨h₁, h₀⟩


-- created on 2020-03-20
