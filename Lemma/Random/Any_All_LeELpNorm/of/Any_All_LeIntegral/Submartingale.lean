import Mathlib.Probability.Martingale.Basic
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [m₀ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ m₀}
  {f : ℕ → Ω → ℝ}
-- given
  (h₀ : Submartingale f ℱ μ)
  (h₁ : ∃ R : ℝ, ∀ n, ∫ ω, (f n ω)⁺ ∂μ ≤ R) :
-- imply
  ∃ R : NNReal, ∀ n, eLpNorm (f n) 1 μ ≤ R := by
-- proof
  obtain ⟨R, hR⟩ := h₁
  refine ⟨(2 * R - ∫ ω, f 0 ω ∂μ).toNNReal, fun n => ?_⟩
  have hint := h₀.integrable n
  have hle : ∫ ω, f 0 ω ∂μ ≤ ∫ ω, f n ω ∂μ := by
    simpa using h₀.setIntegral_le (Nat.zero_le n) MeasurableSet.univ
  have habs : ∫ ω, ‖f n ω‖ ∂μ = 2 * ∫ ω, (f n ω)⁺ ∂μ - ∫ ω, f n ω ∂μ := by
    rw [← integral_const_mul, ← integral_sub (show Integrable (fun ω => 2 * (f n ω)⁺) μ from hint.pos_part.const_mul 2) hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have h₁ := posPart_sub_negPart (f n ω)
    have h₂ := posPart_add_negPart (f n ω)
    simp only [Real.norm_eq_abs]
    linarith
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hint]
  exact ENNReal.ofReal_le_ofReal (by linarith [hR n])


-- created on 2026-09-26