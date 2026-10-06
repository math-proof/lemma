import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Ioo a b = ∅) :
-- imply
  b ≤ a := by
-- proof
  exact not_lt.mp (Set.Ioo_eq_empty_iff.mp h)


-- created on 2021-05-03
