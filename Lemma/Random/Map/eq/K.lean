import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Map
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Stage law recursion of the trajectory model `M`: `law(ω[t+1]) = K θ ∘ₘ law(ω[t])`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t : ℕ) :
-- imply
  (M θ).map (fun ω => ω (t + 1)) = M.K θ ∘ₘ (M θ).map (fun ω => ω t) := by
-- proof
  have h := congrArg (Measure.map Prod.snd) (Random.Map (M := M) θ t)
  rw [Measure.map_map measurable_snd (by fun_prop)] at h
  have h₂ := Measure.snd_compProd ((M θ).map (fun ω => ω t)) (M.K θ)
  rw [Measure.snd] at h₂
  rw [← h₂, ← h]
  rfl


-- created on 2026-10-07
