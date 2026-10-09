import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Pn0.eq.Eq
import Lemma.Random.PnAdd_1.eq.Sum_MulProbSum_MulTPn
import Lemma.Random.Pn1.eq.P1
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
Chapman–Kolmogorov: `Pr(s[n+1] = z | s[0] = x) = ∑ y, Pr(s[n] = y | s[0] = x) * Pr(s[1] = z | s[0] = y)`
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (n : ℕ)
  (x z : S) :
-- imply
  M.Pn θ (n + 1) x z = ∑ y, M.Pn θ n x y * M.P1 θ y z := by
-- proof
  induction n generalizing x with
  | zero =>
    rw [Random.Pn1.eq.P1]
    simp [Random.Pn0.eq.Eq]
  | succ n ih =>
    calc M.Pn θ (n + 1 + 1) x z
        = ∑ u, M.pol.prob θ x u * ∑ y', M.T x u y' * M.Pn θ (n + 1) y' z := Random.PnAdd_1.eq.Sum_MulProbSum_MulTPn (M := M) θ (n + 1) x z
      _ = ∑ u, M.pol.prob θ x u * ∑ y', M.T x u y' * ∑ y, M.Pn θ n y' y * M.P1 θ y z := by
          simp_rw [ih]
      _ = ∑ y, (∑ u, M.pol.prob θ x u * ∑ y', M.T x u y' * M.Pn θ n y' y) * M.P1 θ y z := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = ∑ y, M.Pn θ (n + 1) x y * M.P1 θ y z := by
          simp_rw [Random.PnAdd_1.eq.Sum_MulProbSum_MulTPn]


-- created on 2026-10-06
