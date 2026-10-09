import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₁ : a ≤ x)
  (h₂ : x ≤ b) :
-- imply
  Set.Ico a x ∪ Set.Icc x b = Set.Icc a b := by
-- proof
  exact Set.Ico_union_Icc_eq_Icc h₁ h₂


-- created on 2021-05-23
-- updated on 2023-05-12
