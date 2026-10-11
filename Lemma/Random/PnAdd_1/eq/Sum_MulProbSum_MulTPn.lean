import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.Pn.eq.Integral
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


private lemma pn_step [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] (M : Model Θ S A) (θ : Θ) (n : ℕ) (y y' : S) :
  ∫ z, M.Kf θ (fun z => if z.2.1 = y then (1:ℝ) else 0) n z ∂(M.stageK θ y') = M.Pn θ n y' y :=
  (Pn.eq.Integral (M := M) θ n y' y).symm


/--
One-step recursion of the `n`-step state transition of the trajectory model `M`:
`Pn θ (n+1) x y = ∑ u, π_θ(u | x) * ∑ y', T(x, u, y') * Pn θ n y' y`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (n : ℕ)
  (x y : S) :
-- imply
  M.Pn θ (n + 1) x y = ∑ u, M.pol.prob θ x u * ∑ y', (M.env.trans (x, u)).real {y'} * M.Pn θ n y' y := by
-- proof
  rw [Pn.eq.Integral (M := M) θ (n + 1) x y, WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) θ n x]
  refine Finset.sum_congr rfl fun u _ => congrArg (fun inner => M.pol.prob θ x u * inner) ?_
  refine Finset.sum_congr rfl fun y' _ => by rw [pn_step (M := M) θ n y y']


-- created on 2026-10-06
