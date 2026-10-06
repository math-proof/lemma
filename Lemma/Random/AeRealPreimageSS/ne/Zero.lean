import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
almost surely every visited state is reachable
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, (M θ).real (s k ⁻¹' {s k ω}) ≠ 0 := by
-- proof
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have e : {ω : ℕ → ℝ × S × A | ¬ (M θ).real (s (A := A) k ⁻¹' {s k ω}) ≠ 0} =
      ⋃ y ∈ {y : S | (M θ).real (s (A := A) k ⁻¹' {y}) = 0}, s (A := A) k ⁻¹' {y} := by
    ext ω; simp
  rw [e]
  exact (measure_biUnion_null_iff (Set.to_countable _)).2 fun y hy => meas_zero_of_real M θ hy


-- created on 2026-10-06
