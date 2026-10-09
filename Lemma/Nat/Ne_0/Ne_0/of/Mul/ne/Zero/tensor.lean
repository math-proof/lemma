import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
  -- given
  (h : a * b ≠ 0)
  -- imply
  : a ≠ 0 ∧ b ≠ 0 := by
  -- proof
  constructor
  · intro ha
    apply h
    rw [ha]
    simp
  · intro hb
    apply h
    rw [hb]
    simp

-- created on 2018-01-26
