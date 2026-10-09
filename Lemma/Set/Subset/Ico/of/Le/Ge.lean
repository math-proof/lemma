import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x y : ℤ}
-- given
  (h₀ : y ≤ b)
  (h₁ : x ≥ a) :
-- imply
  Set.Ico x (y + 1) ⊆ Set.Ico a (b + 1) :=
-- proof
  Set.Ico_subset_Ico h₁ (by omega)


-- created on 2021-05-18
-- updated on 2023-05-18
