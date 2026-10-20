import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  (h₀ : x ≤ 0) :
-- imply
  Real.sin x ≥ x * (1 - x / Real.pi) := by
-- proof
  set t := -x
  have ht0 : 0 ≤ t := by
    linarith
  have hsin : Real.sin t ≤ t := by
    have h := Real.abs_sin_le_abs (x := t)
    rw [abs_of_nonneg ht0] at h
    exact (abs_le.mp h).2
  have hpoly : Real.sin t ≤ t + t ^ 2 / Real.pi := by
    linarith [div_nonneg (sq_nonneg t) Real.pi_pos.le]
  rw [show x = -t by simp [t], Real.sin_neg]
  have hrhs : -t * (1 - -t / Real.pi) = -t - t ^ 2 / Real.pi := by
    field_simp
    ring
  rw [hrhs]
  linarith


-- created on 2023-10-03
-- updated on 2026-10-17
