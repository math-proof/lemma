import Mathlib.MeasureTheory.Integral.Bochner.Basic
import sympy.Basic
open MeasureTheory


/--
If `∫ f = 1` (e.g. `f` is a probability density) and `‖F u‖ ≤ f u * C` for every `u`, then `‖∫ F‖ ≤ C`.
-/
@[main]
private lemma main
  [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure A}
  {f : A → ℝ}
  {F : A → E}
  {C : ℝ}
-- given
  (h₀ : ∫ u, f u ∂μ = 1)
  (h₁ : ∀ u, ‖F u‖ ≤ f u * C) :
-- imply
  ‖∫ u, F u ∂μ‖ ≤ C := by
-- proof
  have h := norm_integral_le_of_norm_le ((Integrable.of_integral_ne_zero (by rw [h₀]; exact one_ne_zero)).mul_const C)
    (Filter.Eventually.of_forall h₁)
  rwa [integral_mul_const, h₀, one_mul] at h


-- created on 2026-10-07
