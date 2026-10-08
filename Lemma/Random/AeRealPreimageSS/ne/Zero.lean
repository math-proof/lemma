import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Eq_0.of.EqReal_0
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
almost surely every visited state is reachable
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
-- given
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, (M θ).real (s k ⁻¹' {s k ω}) ≠ 0 := by
-- proof
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have e : {ω : ℕ → ℝ × S × A | ¬ (M θ).real (s k ⁻¹' {s k ω}) ≠ 0} =
      ⋃ y ∈ {y : S | (M θ).real (s k ⁻¹' {y}) = 0}, s k ⁻¹' {y} := by
    ext ω; simp
  rw [e]
  exact (measure_biUnion_null_iff (Set.to_countable _)).2 fun y hy => Eq_0.of.EqReal_0 (M := M) θ hy


-- created on 2026-10-06
