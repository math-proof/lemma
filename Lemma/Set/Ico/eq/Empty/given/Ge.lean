import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
-- given
  (h : Finset.Ico a b = ∅) :
-- imply
  b ≤ a := by
-- proof
  exact not_lt.mp (Finset.Ico_eq_empty_iff.mp h)


-- created on 2021-06-15
