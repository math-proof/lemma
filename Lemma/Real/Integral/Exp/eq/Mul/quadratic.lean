import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import sympy.Basic


@[path]
private lemma main
  {a b c : ℝ}
  (h₀ : 0 < a) :
-- imply
  (∫ x : ℝ, Real.exp (-(a * x ^ 2 + b * x + c))) =
    Real.sqrt (Real.pi / a) * Real.exp (b ^ 2 / (4 * a) - c) := by
-- proof
  have hexp (x : ℝ) :
    -(a * x ^ 2 + b * x + c) =
      (b ^ 2 / (4 * a) - c) + -(a * (x + b / (2 * a)) ^ 2) := by
    field_simp [h₀.ne']
    ring
  have hI :
    (∫ x : ℝ, Real.exp (-(a * x ^ 2 + b * x + c))) =
      ∫ x : ℝ, Real.exp (b ^ 2 / (4 * a) - c) *
        Real.exp (-a * (x + b / (2 * a)) ^ 2) := by
    refine congrArg (fun g : ℝ → ℝ => ∫ x, g x) ?_
    funext x
    rw [hexp, Real.exp_add]
    congr 1
    ring_nf
  rw [hI, MeasureTheory.integral_const_mul]
  have htr :
    (∫ x : ℝ, Real.exp (-a * (x + b / (2 * a)) ^ 2)) =
      ∫ x : ℝ, Real.exp (-a * x ^ 2) :=
    MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume)
      (fun u => Real.exp (-a * u ^ 2)) (b / (2 * a))
  rw [htr, integral_gaussian a]
  ring


-- created on 2020-06-11
-- updated on 2026-10-17
