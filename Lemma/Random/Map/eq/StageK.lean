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
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  (M θ).map (fun ω => ω t) = M.stageK θ ∘ₘ (M θ).map (s t) := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  have h₀ : (M θ).map (s t) = ((M θ).map (fun ω => ω t)).map (fun z => z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply t)]; rfl
  rw [h₀]
  cases t with
  | zero =>
    rw [Random.EqMap_Apply, Model.μ₀, Random.EqMapStageK_12]
  | succ t =>
    rw [Map.eq.K, Model.K, ← Measure.comp_assoc, Random.EqMapStageK_12]


-- created on 2026-10-07
