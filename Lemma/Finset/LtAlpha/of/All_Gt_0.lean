import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.K.gt.Zero.of.All_Imp_Gt_0.Gt_0
import Lemma.Finset.SubMulSHK.eq.PowNeg1_Add_1
import Lemma.Finset.Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0
open Finset Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i ≥ 1, x i > 0) :
-- imply
  alpha ((List.range (2 * n - 1)).map x) < alpha ((List.range (2 * n + 1)).map x) := by
-- proof
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega]
  have hp : ∀ m, ∀ j, 1 ≤ j → j < m → 0 < x j := fun _ j hj _ => h j hj
  rw [Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0 x (by omega) (hp _), Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0 x (by omega) (hp _)]
  have hK1 := K.gt.Zero.of.All_Imp_Gt_0.Gt_0 x (2 * k + 1) (by omega) (hp _)
  have hK2 := K.gt.Zero.of.All_Imp_Gt_0.Gt_0 x (2 * k + 1 + 2) (by omega) (hp _)
  have d : H x (2 * k + 1 + 1) * K x (2 * k + 1) - H x (2 * k + 1) * K x (2 * k + 1 + 1) = 1 := by
    rw [SubMulSHK.eq.PowNeg1_Add_1 x (2 * k + 1), show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, neg_one_sq, one_pow]
  have key : H x (2 * k + 1 + 2) * K x (2 * k + 1) - H x (2 * k + 1) * K x (2 * k + 1 + 2) = x (2 * k + 1 + 1) := by
    show (H x (2 * k + 1 + 1) * x (2 * k + 1 + 1) + H x (2 * k + 1)) * K x (2 * k + 1) -
      H x (2 * k + 1) * (K x (2 * k + 1 + 1) * x (2 * k + 1 + 1) + K x (2 * k + 1)) = _
    linear_combination x (2 * k + 1 + 1) * d
  rw [div_lt_div_iff₀ hK1 hK2]
  linarith [h (2 * k + 1 + 1) (by omega)]


-- created on 2021-08-13
