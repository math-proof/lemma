import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient


/--
Where `π_θ(u | x) = 0` (a global minimum of `θ ↦ π_θ(u | x)`), its derivative vanishes.
Continuous-action counterpart of `Random.Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [ReferenceMeasure A]
  {π : Policy Θ S A} [hStoch : StochasticPolicy π]
-- given
  (θ : Θ)
  (sₜ : S)
  (aₜ : A)
  (h₀ : π.π θ sₜ aₜ = 0) :
-- imply
  fderiv ℝ (fun θ' => π.π θ' sₜ aₜ) θ = 0 := by
-- proof
  refine IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun θ' => ?_)
  show π.π θ sₜ aₜ ≤ π.π θ' sₜ aₜ
  rw [h₀]
  exact hStoch.nonneg θ' sₜ aₜ


-- created on 2026-10-20
-- updated on 2026-11-17
