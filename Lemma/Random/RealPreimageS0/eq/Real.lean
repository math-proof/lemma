import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
The law of `s[0]` under the trajectory model is the initial distribution: `Pr(s[0] = x) = init {x}`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (x : S) :
-- imply
  (M θ).real (s 0 ⁻¹' {x}) = M.env.init.real {x} := by
-- proof
  have h : (M θ).map (s 0) = ((M θ).map (fun ω => ω 0)).map (fun z => z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply 0)]; rfl
  rw [measureReal_def, ← Measure.map_apply (s_meas 0) (measurableSet_singleton x), h, stage_zero,
    Model.μ₀, fst_stageK_comp, measureReal_def]


-- created on 2026-10-06
