import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₁ : a < x)
  (h₂ : x ≤ b) :
-- imply
  Set.Ioo a x ∪ Set.Ico x b = Set.Ioo a b := by
-- proof
  exact Set.Ioo_union_Ico_eq_Ioo h₁ h₂


-- created on 2021-06-02
-- updated on 2023-05-20
