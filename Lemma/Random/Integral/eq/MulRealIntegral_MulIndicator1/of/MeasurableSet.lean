import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Conditional integral as a normalized integral: `∫ f ∂(μ[|B]) = μ(B)⁻¹ * ∫ 1_B * f ∂μ`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {B : Set (ℕ → ℝ × S × A)}
-- given
  (hB : MeasurableSet B)
  (θ : Θ)
  (f : (ℕ → ℝ × S × A) → ℝ) :
-- imply
  ∫ ω, f ω ∂(M θ)[|B] = ((M θ).real B)⁻¹ * ∫ ω, B.indicator 1 ω * f ω ∂(M θ) := by
-- proof
  rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hB, ENNReal.toReal_inv,
    ← measureReal_def, smul_eq_mul]
  congr 1
  congr 1
  funext ω
  by_cases h : ω ∈ B <;> simp [h]


-- created on 2026-10-07
