import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.EqMapStageK_12
import Lemma.Random.EqMap_Apply
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


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
  (M θ).real (state 0 ⁻¹' {x}) = M.env.init.real {x} := by
-- proof
  have h : (M θ).map (state 0) = ((M θ).map (fun ω => ω 0)).map (fun z => z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply 0)]; rfl
  rw [measureReal_def, ← Measure.map_apply (Random.Measurable_S 0) (measurableSet_singleton x), h, Random.EqMap_Apply,
    Model.μ₀, Random.EqMapStageK_12, measureReal_def]


-- created on 2026-10-06
