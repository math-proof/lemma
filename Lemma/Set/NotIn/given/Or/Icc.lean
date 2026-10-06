import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h : x ∉ Set.Ico a b) :
-- imply
  x = b ∨ x ∉ Set.Icc a b := by
-- proof
  if hxb : x = b then
    exact Or.inl hxb
  else
    apply Or.inr
    intro hmem
    exact h ⟨hmem.1, lt_of_le_of_ne hmem.2 hxb⟩


-- created on 2020-10-20
