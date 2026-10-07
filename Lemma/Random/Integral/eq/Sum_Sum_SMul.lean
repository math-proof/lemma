import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
import Lemma.Random.RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`𝔼[φ(s[t], a[t])] = ∑ y, ∑ u, (Pr(s[t] = y) * π_θ(u | y)) • φ y u` under the trajectory model.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {E : Type*}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [CompleteSpace E]
-- given
  (θ : Θ)
  (t : ℕ)
  (φ : S → A → E) :
-- imply
  ∫ ω, φ (s t ω) (a t ω) ∂(M θ) =
    ∑ y, ∑ u, ((M θ).real (s t ⁻¹' {y}) * M.pol.prob θ y u) • φ y u := by
-- proof
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) := (Random.Measurable_S t).prodMk (Random.Measurable_A t)
  have e := integral_map (μ := M θ) hX.aemeasurable
    (f := fun p : S × A => φ p.1 p.2) StronglyMeasurable.of_discrete.aestronglyMeasurable
  refine e.symm.trans ?_
  rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun u _ => ?_
  rw [map_measureReal_apply hX (measurableSet_singleton _), ← RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb]
  congr 2
  ext ω
  simp [Prod.ext_iff]


-- created on 2026-10-06
