import Mathlib.Data.Int.Basic
import sympy.Basic


@[path]
private lemma main
  {x a : ℤ}
  -- given
  (h : |x| < a)
  -- imply
  : x < a ∧ -a < x := by
  -- proof
  rw [abs_lt] at h
  exact ⟨h.2, h.1⟩

-- created on 2019-12-28
