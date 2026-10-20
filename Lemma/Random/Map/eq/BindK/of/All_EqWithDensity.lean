import Lemma.Random.Map.eq.CompProd.of.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
Stage law recursion of the continuous-action trajectory model `M`: `law(ω[t+1]) = K θ ∘ₘ law(ω[t])`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
-- given
  (θ : Θ)
  (t : ℕ) :
-- imply
  (M θ).map (fun ω => ω (t + 1)) = M.K θ ∘ₘ (M θ).map (fun ω => ω t) := by
-- proof
  have h := congrArg (Measure.map Prod.snd) (Map.eq.CompProd.of.All_EqWithDensity (M := M) θ t)
  rw [Measure.map_map measurable_snd (by fun_prop)] at h
  have h₂ := Measure.snd_compProd ((M θ).map (fun ω => ω t)) (M.K θ)
  rw [Measure.snd] at h₂
  rw [← h₂, ← h]
  rfl


-- created on 2026-10-20
