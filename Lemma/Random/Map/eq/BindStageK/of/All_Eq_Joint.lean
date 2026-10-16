import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.EqMapStageK_12
import Lemma.Random.Map.eq.BindStageK
import Lemma.Random.Map.eq.BindK
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
The stage `ω[t]` is distributed as `stageK θ ∘ₘ law(s[t])`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  (M θ).map (fun ω => ω t) = M.stageK θ ∘ₘ (M θ).map (s t) := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  have h : (M θ).map (s t) = ((M θ).map (fun ω => ω t)).map (fun z => z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply t)]; rfl
  rw [h]
  cases t with
  | zero =>
    rw [Map.eq.BindStageK, EqMapStageK_12]
  | succ t =>
    rw [Map.eq.BindK, Model.K, ← Measure.comp_assoc, EqMapStageK_12]


-- created on 2026-10-13
