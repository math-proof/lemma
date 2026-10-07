import Mathlib
import sympy.Basic
open Set



@[main]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hf : ContinuousOn f (Icc a b)) :
-- imply
  ∃ ε ∈ Ioo (0 : ℝ) 1, ∫ x in a..b, f x = (b - a) * f (a * ε + b * (1 - ε)) := by
-- proof
  sorry


-- created on 2026-10-07
