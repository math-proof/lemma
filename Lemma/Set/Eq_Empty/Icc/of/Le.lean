import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  Set.Ico y x = ∅ := by
-- proof
  exact Set.Ico_eq_empty_of_le h


-- created on 2019-07-09
