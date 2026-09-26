import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
-- given
  (X : Ω → ℝ)
  (B : Set Ω) :
-- imply
  (∫ ω, X ω ∂μ[|B]) * μ.real B = ∫ ω in B, X ω ∂μ := by
-- proof
  if h : μ B = 0 then
    rw [cond_eq_zero_of_meas_eq_zero h, integral_zero_measure, zero_mul, setIntegral_measure_zero _ h]
  else
    rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv, measureReal_def, mul_comm, mul_inv_cancel_left₀ (ENNReal.toReal_ne_zero.mpr ⟨h, measure_ne_top μ B⟩)]


-- created on 2026-09-26
