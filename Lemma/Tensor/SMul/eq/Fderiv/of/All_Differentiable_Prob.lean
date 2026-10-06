import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Tensor.Fderiv_Prob.eq.Zero.of.EqProb_0
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
`π_θ(u | x) • fderiv log π_θ(u | x) = fderiv π_θ(u | x)` (also where `π_θ(u | x) = 0`).
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (θ : Θ)
  (x : S)
  (u : A) :
-- imply
  M.pol.prob θ x u • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' x u)) θ =
    fderiv ℝ (fun θ' => M.pol.prob θ' x u) θ := by
-- proof
  by_cases h : M.pol.prob θ x u = 0
  · rw [h, zero_smul, Tensor.Fderiv_Prob.eq.Zero.of.EqProb_0 (M := M) θ x u h]
  · rw [fderiv.log ((h₀ x u) θ) h, smul_smul, mul_inv_cancel₀ h, one_smul]


-- created on 2026-10-06
