import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`𝔼[φ(s[t])] = ∑ y, Pr(s[t] = y) • φ y` under the trajectory model.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {E : Type*}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [CompleteSpace E]
-- given
  (θ : Θ)
  (t : ℕ)
  (φ : S → E) :
-- imply
  ∫ ω, φ (state t ω) ∂(M θ) = ∑ y, (M θ).real (state t ⁻¹' {y}) • φ y := by
-- proof
  have e := integral_map (μ := M θ) (Random.Measurable_S t).aemeasurable
    (f := φ) StronglyMeasurable.of_discrete.aestronglyMeasurable
  refine e.symm.trans ?_
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_measureReal_apply (Random.Measurable_S t) (measurableSet_singleton _)]


-- created on 2026-10-06
