import sympy.sets.sets
import sympy.Basic


@[main]
private lemma upper
  {a b : ℝ} :
-- imply
  Set.Icc |a| b ⊆ Set.Icc a b := by
-- proof
  exact Set.Icc_subset_Icc_left (le_abs_self a)


-- created on 2019-09-06
