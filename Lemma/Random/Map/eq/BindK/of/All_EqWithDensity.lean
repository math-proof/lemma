import Lemma.Random.Map.eq.CompProd.of.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Stage law recursion of the continuous-action trajectory model `M`: `law(ω[t+1]) = K θ ∘ₘ law(ω[t])`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (t : ℕ) :
-- imply
  (M.traj θ).map (fun ω => ω (t + 1)) = M.K θ ∘ₘ (M.traj θ).map (fun ω => ω t) := by
-- proof
  have h := congrArg (Measure.map Prod.snd) (Map.eq.CompProd.of.All_EqWithDensity (M := M) θ t)
  rw [Measure.map_map measurable_snd (by fun_prop)] at h
  have h₂ := Measure.snd_compProd ((M.traj θ).map (fun ω => ω t)) (M.K θ)
  rw [Measure.snd] at h₂
  rw [← h₂, ← h]
  rfl


-- created on 2026-10-20
-- updated on 2026-11-16
