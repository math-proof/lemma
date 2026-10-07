import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Tensor.SMul.eq.Fderiv.of.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
zero expected score: `∑ u, π_θ(u | x) • ∇ log π_θ(u | x) = 0` (no positivity needed)
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (θ : Θ)
  (x : S) :
-- imply
  ∑ u, M.pol.prob θ x u • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' x u)) θ = 0 := by
-- proof
  simp_rw [Tensor.SMul.eq.Fderiv.of.All_Differentiable_Prob (M := M) h₀ θ x]
  rw [← fderiv_fun_sum fun u _ => (h₀ x u) θ]
  simp_rw [M.pol.sum_eq_one]
  exact fderiv_const_apply 1


-- created on 2026-10-06
