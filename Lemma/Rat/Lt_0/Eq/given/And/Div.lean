import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
  -- given
  (h : a = b)
  (hneg : c < 0)
  -- imply
  : a / c = b / c := by
  -- proof
  rw [h]

-- created on 2023-03-26
