import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Ioo a b = ∅) :
-- imply
  0 ≤ a - b := by
-- proof
  have hle : b ≤ a := not_lt.mp (Set.Ioo_eq_empty_iff.mp h)
  linarith


-- created on 2021-05-04
