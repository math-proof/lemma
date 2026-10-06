import sympy.Basic


@[main]
private lemma main
  {a b t : ℝ}
-- given
  (h : b < a) :
-- imply
  b - t < a - t ∧ t ∈ (Set.univ : Set ℝ) := by
-- proof
  constructor
  · linarith
  · trivial


-- created on 2021-04-15
