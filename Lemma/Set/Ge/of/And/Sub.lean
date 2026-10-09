import sympy.Basic


@[path]
private lemma main
  {a b t : ℝ}
-- given
  (h : b ≤ a) :
-- imply
  b - t ≤ a - t ∧ t ∈ (Set.univ : Set ℝ) := by
-- proof
  constructor
  · exact sub_le_sub_right h t
  · trivial


-- created on 2021-04-08
