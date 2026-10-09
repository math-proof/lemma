import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.EqMapStageK_12
import Lemma.Random.EqMap_Apply
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
The law of `s[0]` under the trajectory model is the initial distribution: `Pr(s[0] = x) = init {x}`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (x : S) :
-- imply
  (M θ).real (s 0 ⁻¹' {x}) = M.env.init.real {x} := by
-- proof
  have hs : s 0 = fun ω ↦ (ω 0).2.1 := funext fun ω ↦ (congrArg (·.2.1) (congrFun (h₁ 0) ω)).symm
  have h : (M θ).map (s 0) = ((M θ).map (fun ω => ω 0)).map (fun z => z.2.1) := by
    rw [hs, Measure.map_map measurable_snd.fst (measurable_pi_apply 0)]; rfl
  rw [measureReal_def, ← Measure.map_apply (Random.Measurable_S h₁ 0) (measurableSet_singleton x), h, Random.EqMap_Apply,
    Model.μ₀, Random.EqMapStageK_12, measureReal_def]


-- created on 2026-10-06
