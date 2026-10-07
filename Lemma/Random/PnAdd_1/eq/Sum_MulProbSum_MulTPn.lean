import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
One-step recursion of the `n`-step state transition of the trajectory model `M`:
`Pn θ (n+1) x y = ∑ u, π_θ(u | x) * ∑ y', T(x, u, y') * Pn θ n y' y`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (n : ℕ)
  (x y : S) :
-- imply
  M.Pn θ (n + 1) x y = ∑ u, M.pol.prob θ x u * ∑ y', M.T x u y' * M.Pn θ n y' y := by
-- proof
  exact WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) θ n x


-- created on 2026-10-06
