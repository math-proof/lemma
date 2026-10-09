import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.K.gt.Zero.of.All_Imp_Gt_0.Gt_0
import Lemma.Finset.SubMulSHK.eq.PowNeg1_Add_1
import Lemma.Finset.Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0
open Finset Continuant


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i ≥ 1, x i > 0) :
-- imply
  alpha ((List.range (2 * n)).map x) > alpha ((List.range (2 * n + 2)).map x) := by
-- proof
  have hp : ∀ m, ∀ j, 1 ≤ j → j < m → 0 < x j := fun _ j hj _ => h j hj
  rw [Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0 x (by omega) (hp _), Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0 x (by omega) (hp _)]
  have hK1 := K.gt.Zero.of.All_Imp_Gt_0.Gt_0 x (2 * n) (by omega) (hp _)
  have hK2 := K.gt.Zero.of.All_Imp_Gt_0.Gt_0 x (2 * n + 2) (by omega) (hp _)
  have d : H x (2 * n + 1) * K x (2 * n) - H x (2 * n) * K x (2 * n + 1) = -1 := by
    rw [SubMulSHK.eq.PowNeg1_Add_1 x (2 * n), pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  have key : H x (2 * n + 2) * K x (2 * n) - H x (2 * n) * K x (2 * n + 2) = -x (2 * n + 1) := by
    show (H x (2 * n + 1) * x (2 * n + 1) + H x (2 * n)) * K x (2 * n) -
      H x (2 * n) * (K x (2 * n + 1) * x (2 * n + 1) + K x (2 * n)) = _
    linear_combination x (2 * n + 1) * d
  rw [gt_iff_lt, div_lt_div_iff₀ hK2 hK1]
  linarith [h (2 * n + 1) (by omega)]


-- created on 2021-09-13
