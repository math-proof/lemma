import sympy.sets.sets
import sympy.Basic


@[main]
private lemma upper
  {a u : ℝ}
-- given
  (h : a ≤ 0) :
-- imply
  Set.Icc (-a) u ⊆ Set.Icc a u := by
-- proof
  exact Set.Icc_subset_Icc_left (by linarith)


-- created on 2026-09-27
