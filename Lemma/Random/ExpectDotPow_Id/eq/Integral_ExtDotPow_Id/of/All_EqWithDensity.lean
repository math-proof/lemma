import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory PolicyGradient PolicyGradient.Model Random Measure


/--
Discounted return under the continuous-action path binder:
`𝔼[r: M θ]((γ ^ id) ⬝ᵥ r)` is the Bochner integral of the same observable.
Continuous-action counterpart of [discounted return under the path binder](?module=Random.ExpectDotPow_Id.eq.Integral_ExtDotPow_Id).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M] {θ : Θ} {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ} [PSpace (M θ) (AsPathRV.path r)] :
-- imply
  𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) ω ∂(M θ) := by
-- proof
  apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun path : ℕ → ℝ ↦ ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ path))
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun t ↦
    (measurable_pi_apply t).const_mul (γ ^ t)).aestronglyMeasurable


-- created on 2026-10-20
-- updated on 2026-11-18