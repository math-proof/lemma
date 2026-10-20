import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Lemma.Random.Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient Random


/--
`π_θ(u | x) • fderiv log π_θ(u | x) = fderiv π_θ(u | x)` (also where `π_θ(u | x) = 0`).
Continuous-action counterpart of
`Random.EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb`
(no `[Fintype A]`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (θ : Θ)
  (x : S)
  (u : A) :
-- imply
  M.policy.prob θ x u • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' x u)) θ =
    fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ := by
-- proof
  if h : M.policy.prob θ x u = 0 then
    rw [h, zero_smul, Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0.All_EqWithDensity
      (π := M.policy) θ x u h]
  else
    rw [fderiv.log ((h₀ x u) θ) h, smul_smul, mul_inv_cancel₀ h, one_smul]


-- created on 2026-10-20
