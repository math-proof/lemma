import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Theorem.Probability.CondExpectation
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The observation form of `V` agrees with the Bochner integral of the discounted return
against the conditional measure `(M.traj θ)[| s t ⁻¹' {x}]`, on atoms of positive mass.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {θ : Θ}
  {t : ℕ}
  {sₜ : 𝒮}
-- given
  (h₀ : Measurable (fun ω t ↦ r t ω))
  (hs : Measurable (s t))
  (hx : (M.traj θ) (s t ⁻¹' {sₜ}) ≠ 0)
  (γ : ℝ) :
-- imply
  𝔼[r : M.traj θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = sₜ) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω ∂(M.traj θ)[|s t ⁻¹' {sₜ}] := by
-- proof
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hpos : (M.traj θ).map (s t) {sₜ} ≠ 0 :=
    (Measure.map_apply hs (measurableSet_singleton sₜ)).symm ▸ hx
  simp only [Expectation.asRV_process]
  exact Expectation.condEval_eq_integral h₀ hs hfG hpos


-- created on 2026-10-11
-- updated on 2026-11-17