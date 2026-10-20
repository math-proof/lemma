import Mathlib.Analysis.Calculus.LocalExtr.Basic
import sympy.stats.policy_trajectory.continuous_action
open MeasureTheory ProbabilityTheory Topology PolicyGradient


/--
Where `π_θ(u | x) = 0` (a global minimum of `θ ↦ π_θ(u | x)`), its derivative vanishes.
Continuous-action counterpart of `Random.Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [ReferenceMeasure A]
  {π : DensityPolicy Θ S A}
-- given
  (θ : Θ)
  (x : S)
  (u : A)
  (h₀ : π.prob θ x u = 0) :
-- imply
  fderiv ℝ (fun θ' => π.prob θ' x u) θ = 0 := by
-- proof
  refine IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun θ' => ?_)
  show π.prob θ x u ≤ π.prob θ' x u
  rw [h₀]
  exact π.nonneg θ' x u


-- created on 2026-10-20
