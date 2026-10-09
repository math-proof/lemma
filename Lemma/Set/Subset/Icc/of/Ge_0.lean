import sympy.sets.sets
import sympy.Basic


@[path]
private lemma lower
  {a l : ℝ}
-- given
  (h : a ≥ 0) :
-- imply
  Set.Icc l (-a) ⊆ Set.Icc l a := by
-- proof
  exact Set.Icc_subset_Icc_right (by linarith)


-- created on 2019-07-10
