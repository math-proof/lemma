import Lemma.Random.Pn1.eq.P1
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


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
    rw [Pn1.eq.P1]
    simp [Pn0.eq.Eq]
  | succ n ih =>
    calc
      _ = ∑ u, M.policy.prob θ x u * ∑ y', (M.env.trans (x, u)).real {y'} * M.Pn θ (n + 1) y' z :=
        PnAdd_1.eq.Sum_MulProbSum_MulTPn (M := M) θ (n + 1) x z
      _ = ∑ u, M.policy.prob θ x u * ∑ y', (M.env.trans (x, u)).real {y'} * ∑ y, M.Pn θ n y' y * M.P1 θ y z := by
        simp_rw [ih]
      _ = ∑ y, (∑ u, M.policy.prob θ x u * ∑ y', (M.env.trans (x, u)).real {y'} * M.Pn θ n y' y) * M.P1 θ y z := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun y _ => ?_
        ring
      _ = ∑ y, M.Pn θ (n + 1) x y * M.P1 θ y z := by
        simp_rw [PnAdd_1.eq.Sum_MulProbSum_MulTPn]


-- created on 2026-10-06
