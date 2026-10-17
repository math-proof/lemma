import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Int.Interval
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
-- given
  (h : Set.Ico a b = ∅) :
-- imply
  b ≤ a :=
-- proof
  le_of_not_gt ((Set.Ico_eq_empty_iff).mp h)


-- created on 2021-06-23
-- updated on 2026-10-17
