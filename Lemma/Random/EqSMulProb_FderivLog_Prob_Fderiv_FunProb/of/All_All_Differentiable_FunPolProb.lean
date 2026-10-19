import Lemma.Random.Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
`π_θ(u | x) • fderiv log π_θ(u | x) = fderiv π_θ(u | x)` (also where `π_θ(u | x) = 0`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (θ : Θ)
  (x : S)
  (u : A) :
-- imply
  M.policy.prob θ x u • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' x u)) θ =
    fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ := by
-- proof
  by_cases h : M.policy.prob θ x u = 0
  · rw [h, zero_smul, Random.Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0 (M := M) θ x u h]
  · rw [fderiv.log ((h₀ x u) θ) h, smul_smul, mul_inv_cancel₀ h, one_smul]


-- created on 2026-10-06
