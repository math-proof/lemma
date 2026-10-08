import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.EqMapStageK_12
import Lemma.Random.EqMap_Apply
import Lemma.Random.Map.eq.K
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
The stage `ω[t]` is distributed as `stageK θ ∘ₘ law(s[t])`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t : ℕ) :
-- imply
  (M θ).map (fun ω => ω t) = M.stageK θ ∘ₘ (M θ).map (state t) := by
-- proof
  have h₀ : (M θ).map (state t) = ((M θ).map (fun ω => ω t)).map (fun z => z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply t)]; rfl
  rw [h₀]
  cases t with
  | zero =>
    rw [Random.EqMap_Apply, Model.μ₀, Random.EqMapStageK_12]
  | succ t =>
    rw [Map.eq.K, Model.K, ← Measure.comp_assoc, Random.EqMapStageK_12]


-- created on 2026-10-07
