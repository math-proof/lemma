import sympy.sets.sets
import sympy.Basic


@[path]
private lemma lower
  {a b : ℝ} :
-- imply
  Set.Icc a b ⊆ Set.Icc a |b| := by
-- proof
  exact Set.Icc_subset_Icc_right (le_abs_self b)


-- created on 2019-07-09
