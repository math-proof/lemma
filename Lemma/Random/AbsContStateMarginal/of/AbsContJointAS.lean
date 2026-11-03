import Class.Dynamics.PolicyTrajectory.ContinuousAction
import Mathlib.MeasureTheory.Measure.Prod
open MeasureTheory PolicyGradient PolicyGradient.DensityModel


/--
Joint absolute continuity of `law(a[t], s[t])` w.r.t. the product reference measure
implies absolute continuity of the state marginal `law(s[t])` w.r.t. the reference
measure on `S` (`μ.map Prod.snd ≪ (α.univ) • ν` and `c • ν ≪ ν`).
-/
@[path]
private lemma main
  [ReferenceMeasure S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
  [htr : DensityModel.IsPolicyTrajectory M r s a]
  [haj : DensityModel.AbsContJointAS M a s] :
  DensityModel.AbsContStateMarginal M s := by
-- proof
  refine ⟨fun θ t => ?_⟩
  have hmeas : Measurable fun ω => (a t ω, s t ω) :=
    (htr.measurable_a t).prodMk (htr.measurable_s t)
  have hmap : (M θ).map (s t) =
      ((M θ).map (fun ω => (a t ω, s t ω))).map Prod.snd := by
    rw [Measure.map_map measurable_snd hmeas]
    rfl
  rw [hmap]
  refine ((haj.map_as_ac θ t).map measurable_snd).trans ?_
  rw [Measure.map_snd_prod]
  exact Measure.smul_absolutelyContinuous


-- created on 2026-11-03
