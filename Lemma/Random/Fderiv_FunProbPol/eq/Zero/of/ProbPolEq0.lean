import sympy.stats.policy_trajectory.gradient
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
Where `π_θ(u | x) = 0` (a global minimum of `θ ↦ π_θ(u | x)`), its derivative vanishes.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (x : S)
  (u : A)
  (h₀ : M.policy.prob θ x u = 0) :
-- imply
  fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ = 0 := by
-- proof
  refine IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun θ' => ?_)
  show M.policy.prob θ x u ≤ M.policy.prob θ' x u
  rw [h₀]
  exact M.policy.nonneg θ' x u


-- created on 2026-10-06
