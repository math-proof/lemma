import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
  -- given
  (hx : x ≠ 0)
  (hne : x * a ≠ b)
  -- imply
  : a ≠ b / x := by
  -- proof
  intro h
  apply hne
  calc x * a = x * (b / x) := by rw [h]
    _ = b := by field_simp [hx]

-- created on 2020-02-16
