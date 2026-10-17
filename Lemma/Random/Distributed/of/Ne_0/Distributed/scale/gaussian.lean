import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Probability.Distributions.Gaussian.Real
import sympy.Basic
open MeasureTheory ProbabilityTheory
open scoped NNReal


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
  {μ : ℝ} {v : ℝ≥0}
  {a b : ℝ}
-- given
  (h₀ : a ≠ 0)
  (hx : AEMeasurable x π)
  (h₁ : π.map x = gaussianReal μ v) :
-- imply
  π.map (fun ω => a * x ω + b) =
    gaussianReal (a * μ + b) (.mk (a ^ 2) (sq_nonneg a) * v) := by
-- proof
  have h₂ : a * a⁻¹ = 1 := mul_inv_cancel₀ h₀
  have h₃ : (fun y : ℝ => a * y + b) = (fun y => y + b) ∘ fun y => a * y := by
    ext y
    rw [Function.comp_apply, ← one_mul (a * y), ← h₂]
  rw [show (fun ω => a * x ω + b) = (fun y => a * y + b) ∘ x from rfl,
    ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hx, h₁, h₃,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_add_const]


-- created on 2023-05-03
-- updated on 2026-10-17
