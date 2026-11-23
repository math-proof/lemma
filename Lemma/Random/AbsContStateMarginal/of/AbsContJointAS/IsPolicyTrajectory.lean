import Class.Dynamics.PolicyTrajectory
import Mathlib.MeasureTheory.Measure.Prod
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Instance.Data.Nat.Fun
import Initialize.Tactic.Attr.Basic
open MeasureTheory PolicyGradient PolicyGradient.Model


/--
Joint absolute continuity of `law(a[t], s[t])` w.r.t. the product reference measure
implies absolute continuity of the state marginal `law(s[t])` w.r.t. the reference
measure on `𝒮` (`μ.map Prod.snd ≪ (α.univ) • ν` and `c • ν ≪ ν`).
-/
@[path]
private lemma main
  [ReferenceMeasure 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : Model.IsPolicyTrajectory M r s a)
  (h₁ : Model.AbsContJointAS M a s) :
-- imply
  Model.AbsContStateMarginal M s := by
-- proof
  refine ⟨fun θ t => ?_⟩
  have hmeas : Measurable fun ω => (a t ω, s t ω) :=
    (h₀.measurable_a t).prodMk (h₀.measurable_s t)
  have hmap : (M θ).map (s t) =
      ((M θ).map (fun ω => (a t ω, s t ω))).map Prod.snd := by
    rw [Measure.map_map measurable_snd hmeas]
    rfl
  rw [hmap]
  refine ((h₁.map_as_ac θ t).map measurable_snd).trans ?_
  simpa [Measure.map_snd_prod] using Measure.smul_absolutelyContinuous


-- created on 2026-11-03
-- updated on 2026-11-23