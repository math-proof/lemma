import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {f : ℕ → Ω → ℝ}
-- given
  (h₀ : ∀ n, Integrable (f n) μ)
  (h₁ : ∀ n, 0 ≤ᵐ[μ] f n)
  (h₂ : Summable fun n => ∫ ω, f n ω ∂μ) :
-- imply
  ∀ᵐ ω ∂μ, Summable fun n => f n ω := by
-- proof
  have hm : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (f n ω)) μ := fun n => (h₀ n).aemeasurable.ennreal_ofReal
  have hlt : ∀ᵐ ω ∂μ, ∑' n, ENNReal.ofReal (f n ω) < ⊤ := by
    refine ae_lt_top' (AEMeasurable.tsum hm) ?_
    rw [lintegral_tsum hm]
    calc
      _ = ∑' n, ENNReal.ofReal (∫ ω, f n ω ∂μ) := tsum_congr fun n => (ofReal_integral_eq_lintegral_ofReal (h₀ n) (h₁ n)).symm
      _ = ENNReal.ofReal (∑' n, ∫ ω, f n ω ∂μ) := (ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg_of_ae (h₁ n)) h₂).symm
      _ ≠ ⊤ := ENNReal.ofReal_ne_top
  filter_upwards [hlt, ae_all_iff.2 h₁] with ω hω hnn
  exact (ENNReal.summable_toReal hω.ne).congr fun n => ENNReal.toReal_ofReal (hnn n)


-- created on 2026-09-26