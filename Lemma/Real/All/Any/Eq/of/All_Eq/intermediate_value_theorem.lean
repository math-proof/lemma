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
  ∀ y ∈ Icc (min (f a) (f b)) (max (f a) (f b)), ∃ x ∈ Icc a b, f x = y := by
-- proof
  sorry


-- created on 2026-10-07
