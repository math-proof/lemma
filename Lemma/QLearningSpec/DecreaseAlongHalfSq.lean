import sympy.stats.q_learning
import sympy.stats.lyapunov
import sympy.vector.lp_space
import sympy.Basic
import Lemma.QLearningSpec.MulPowCardη.lt.One
import Lemma.QLearningSpec.Gtμmin_0AndGeη_0AndLtη_1
import Lemma.QLearningSpec.NormSubOfLpExpectedUpdateTarget.le.MulηNormSub
import Lemma.LpSpace.Norm.le.MulPow_NormOfLp.of.Ge_1
import Lemma.LpSpace.NormOfLp.le.Norm.of.Ge_1
import Lemma.LpSpace.SumMulAbsHalfSq'_Abs.le.MulNormS.of.Ge_2
import Lemma.LpSpace.InnerToL2HalfSq'_ToL2.eq.SquareNorm.of.Ge_1
open Finset LpSpace


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {spec : QLearningSpec S A} :
-- imply
  DecreaseAlong (fun x : EuclideanVec (Fintype.card (S × A)) => half_sq (ofL2 spec.pmin x)) (fun x => (half_sq' (ofL2 spec.pmin x)).toL2) spec.expected_update_target := by
-- proof
  have h2p : 2 ≤ spec.pmin := le_max_left _ _
  have h1p : 1 ≤ spec.pmin := by omega
  have : Fact (1 ≤ (spec.pmin : ENNReal)) := ⟨by exact_mod_cast h1p⟩
  have hc := QLearningSpec.MulPowCardη.lt.One (spec := spec)
  obtain ⟨-, hη0, -⟩ := QLearningSpec.Gtμmin_0AndGeη_0AndLtη_1 (spec := spec)
  refine ⟨⟨2 * (1 - (Fintype.card (S × A) : ℝ) ^ (1 / (spec.pmin : ℝ)) * spec.η), by linarith, fun z hz x => ?_⟩⟩
  set V := ofL2 spec.pmin (x - z) with hV
  have hxz : x - z = V.toL2 := rfl
  have e : spec.expected_update_target x - x = (spec.expected_update_target x - spec.expected_update_target z) + -V.toL2 := by
    rw [← hz, ← hxz]
    abel
  have hW : inner ℝ (half_sq' V).toL2 (spec.expected_update_target x - spec.expected_update_target z) ≤
      ∑ i, |half_sq' V i| * |ofL2 spec.pmin (spec.expected_update_target x - spec.expected_update_target z) i| := by
    rw [PiLp.inner_apply]
    exact sum_le_sum fun i _ => real_inner_le_norm _ _
  have hY : ‖ofL2 spec.pmin (spec.expected_update_target x - spec.expected_update_target z)‖ ≤ (Fintype.card (S × A) : ℝ) ^ (1 / (spec.pmin : ℝ)) * (spec.η * ‖V‖) :=
    (LpSpace.Norm.le.MulPow_NormOfLp.of.Ge_1 h1p).trans (mul_le_mul_of_nonneg_left
      ((QLearningSpec.NormSubOfLpExpectedUpdateTarget.le.MulηNormSub x z).trans (mul_le_mul_of_nonneg_left (LpSpace.NormOfLp.le.Norm.of.Ge_1 h1p) hη0)) (by positivity))
  have hI := hW.trans ((LpSpace.SumMulAbsHalfSq'_Abs.le.MulNormS.of.Ge_2 h2p).trans (mul_le_mul_of_nonneg_left hY (norm_nonneg _)))
  show inner ℝ (half_sq' V).toL2 (spec.expected_update_target x - x) ≤ -(2 * (1 - (Fintype.card (S × A) : ℝ) ^ (1 / (spec.pmin : ℝ)) * spec.η)) * half_sq V
  rw [e, inner_add_right, inner_neg_right, LpSpace.InnerToL2HalfSq'_ToL2.eq.SquareNorm.of.Ge_1 h1p, LpSpace.half_sq]
  linarith


-- created on 2026-09-26
