import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : y ≤ b)
  (h₁ : x ≥ a) :
-- imply
  Set.Icc x y ⊆ Set.Icc a b :=
-- proof
  Set.Icc_subset_Icc h₁ h₀


-- created on 2021-05-17
-- updated on 2023-05-20
