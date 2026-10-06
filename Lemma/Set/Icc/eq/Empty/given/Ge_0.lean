import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Ioc a b = ∅) :
-- imply
  0 ≤ a - b := by
-- proof
  have hle : b ≤ a := not_lt.mp (Set.Ioc_eq_empty_iff.mp h)
  linarith


-- created on 2021-04-30
