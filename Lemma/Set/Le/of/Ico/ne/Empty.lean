import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Int.Interval
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
-- given
  (h : Set.Ico a b ≠ ∅) :
-- imply
  a ≤ b := by
-- proof
  apply le_of_lt
  by_contra hle
  exact h ((Set.Ico_eq_empty_iff).mpr hle)


-- created on 2021-06-23
-- updated on 2026-10-17
