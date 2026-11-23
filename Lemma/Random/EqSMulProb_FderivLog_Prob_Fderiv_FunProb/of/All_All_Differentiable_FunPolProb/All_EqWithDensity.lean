import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Lemma.Random.Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0.All_EqWithDensity
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient Random


/--
`π_θ(u | x) • fderiv log π_θ(u | x) = fderiv π_θ(u | x)` (also where `π_θ(u | x) = 0`).
Continuous-action counterpart of
`Random.EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb`
(no `[Fintype 𝒜]`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy]
-- given
  (h₀ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (θ : Θ)
  (sₜ : 𝒮)
  (aₜ : 𝒜) :
-- imply
  M.π θ sₜ aₜ • fderiv ℝ (fun θ' => Real.log (M.π θ' sₜ aₜ)) θ =
    fderiv ℝ (fun θ' => M.π θ' sₜ aₜ) θ := by
-- proof
  if h : M.π θ sₜ aₜ = 0 then
    rw [h, zero_smul, Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0.All_EqWithDensity
      (π := M.toPolicy) θ sₜ aₜ h]
  else
    rw [fderiv.log ((h₀ sₜ aₜ) θ) h, smul_smul, mul_inv_cancel₀ h, one_smul]


-- created on 2026-10-20
-- updated on 2026-11-17
