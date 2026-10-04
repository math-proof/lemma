import sympy.Basic


@[main]
private lemma main
  {a b t : ℝ}
  {s : Set ℝ}
-- given
  (h : a ≤ b)
  (_h₁ : t ∈ s) :
-- imply
  a - t ≤ b - t := by
-- proof
  exact sub_le_sub_right h t


-- created on 2020-05-19
