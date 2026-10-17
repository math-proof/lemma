import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import sympy.Basic
open intervalIntegral MeasureTheory Set


@[path]
private lemma main
  {f : ℝ → ℝ} {a b : ℝ}
  (h₀ : ∀ x, 0 ≤ f x)
  (h₁ : IntervalIntegrable f volume a b) :
-- imply
  (∫ x in a..b, f x) =
    (if a ≤ b then (1 : ℝ) else -1) *
      ∫ t in Ioi 0, (volume.restrict (uIoc a b)).real {x | t ≤ f x} := by
-- proof
  rw [intervalIntegral_eq_integral_uIoc, smul_eq_mul]
  apply congrArg (fun z : ℝ => (if a ≤ b then (1 : ℝ) else -1) * z)
  apply Integrable.integral_eq_integral_meas_le
  · simpa [intervalIntegrable_iff, IntegrableOn] using h₁
  ·
    apply ae_of_all
    intro x
    apply h₀


-- created on 2026-10-11
-- updated on 2026-10-17
