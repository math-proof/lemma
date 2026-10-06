import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
  -- given
  (h : y ≤ x)
  -- imply
  : 0 ≤ x - y := by
  -- proof
  exact sub_nonneg.mpr h

-- created on 2018-07-03
-- updated on 2023-03-25
