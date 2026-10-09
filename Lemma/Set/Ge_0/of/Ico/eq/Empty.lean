import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
-- given
  (h : Finset.Ico a b = ∅) :
-- imply
  0 ≤ a - b := by
-- proof
  have hle : b ≤ a := not_lt.mp (Finset.Ico_eq_empty_iff.mp h)
  omega


-- created on 2021-06-18
