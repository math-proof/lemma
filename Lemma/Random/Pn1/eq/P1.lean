import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Pn0.eq.Eq
import Lemma.Random.PnAdd_1.eq.Sum_MulProbSum_MulTPn
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
The `1`-step state transition: `Pn θ 1 x y = P1 θ x y = ∑ u, π_θ(u | x) * T(x, u, y)`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (x y : S) :
-- imply
  M.Pn θ 1 x y = M.P1 θ x y := by
-- proof
  rw [Random.PnAdd_1.eq.Sum_MulProbSum_MulTPn]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp [Random.Pn0.eq.Eq]


-- created on 2026-10-06
