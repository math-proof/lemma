import sympy.Basic


@[main]
private lemma geometric_series
  {r : ℝ}
  {n : ℕ}
-- given
  (h : r ≠ 1) :
-- imply
  ∑ k ∈ Finset.range n, r ^ k = (1 - r ^ n) / (1 - r) := by
-- proof
  rw [geom_sum_eq h]
  have h₁ : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have h₂ : r - 1 ≠ 0 := sub_ne_zero.mpr h
  field_simp
  ring


-- created on 2023-04-08
