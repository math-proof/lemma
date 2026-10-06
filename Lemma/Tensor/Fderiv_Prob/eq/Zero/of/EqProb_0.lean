import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
Where `π_θ(u | x) = 0` (a global minimum of `θ ↦ π_θ(u | x)`), its derivative vanishes.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (x : S)
  (u : A)
  (h₀ : M.pol.prob θ x u = 0) :
-- imply
  fderiv ℝ (fun θ' => M.pol.prob θ' x u) θ = 0 := by
-- proof
  refine IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun θ' => ?_)
  show M.pol.prob θ x u ≤ M.pol.prob θ' x u
  rw [h₀]
  exact M.pol.nonneg θ' x u


-- created on 2026-10-06
