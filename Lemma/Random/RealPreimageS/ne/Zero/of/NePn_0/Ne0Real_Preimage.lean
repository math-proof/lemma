import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Pn0.eq.Eq
import Lemma.Random.PnAdd_1.eq.Sum_MulProbSum_MulTPn
import Lemma.Random.RealPreimageS0.eq.Real
import Lemma.Random.RealPreimageS.eq.Sum_MulRealPn
import Lemma.Random.T.ge.Zero
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma Pn_nonneg [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] (M : Model Θ S A) (θ : Θ) (n : ℕ) (x y : S) :
    0 ≤ M.Pn θ n x y := by
  induction n generalizing x with
  | zero =>
    rw [Pn0.eq.Eq]
    split_ifs
    · norm_num
    · norm_num
  | succ n ih =>
    rw [PnAdd_1.eq.Sum_MulProbSum_MulTPn]
    exact Finset.sum_nonneg fun u _ => mul_nonneg (M.pol.nonneg θ x u)
      (Finset.sum_nonneg fun y' _ => mul_nonneg (T.ge.Zero (M := M) x u y') (ih y'))

/--
If `s[0] = x` is reachable and `Pn θ n x y ≠ 0`, then `s[n] = y` is reachable.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (n : ℕ)
  (x y : S)
  (h₀ : (M θ).real (s 0 ⁻¹' {x}) ≠ 0)
  (h₁ : M.Pn θ n x y ≠ 0) :
-- imply
  (M θ).real (s n ⁻¹' {y}) ≠ 0 := by
-- proof
  rw [RealPreimageS.eq.Sum_MulRealPn]
  rw [RealPreimageS0.eq.Real] at h₀
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum
    (f := fun x' => M.env.init.real {x'} * M.Pn θ n x' y)
    (fun x' _ => mul_nonneg measureReal_nonneg (Pn_nonneg M θ n x' y)) (Finset.mem_univ x)))
  exact mul_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm h₀))
    (lt_of_le_of_ne (Pn_nonneg M θ n x y) (Ne.symm h₁))


-- created on 2026-10-06
