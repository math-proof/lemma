import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b c x : α}
-- given
  (h₀ : x ∈ Icc a c)
  (h₁ : c < b) :
-- imply
  x ∈ Ico a b := by
-- proof
  exact ⟨h₀.1, lt_of_le_of_lt h₀.2 h₁⟩


-- created on 2019-06-29
