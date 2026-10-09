import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Ioc a b = ∅) :
-- imply
  b ≤ a := by
-- proof
  exact not_lt.mp (Set.Ioc_eq_empty_iff.mp h)


-- created on 2021-05-05
