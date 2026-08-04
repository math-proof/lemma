import Lemma.Hyperreal.NotInfinitesimalAdd.of.Ge_0.Gt_0
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfinitePos.ou.InfiniteNeg
import Lemma.Hyperreal.InfiniteNeg.is.Infinite.Lt_0
import Lemma.Hyperreal.InfinitePos.is.Infinite.Gt_0
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Nat.GtSquare_0.of.Ne_0
import Lemma.Int.Gt0Mul.of.Lt_0.Gt_0
import Lemma.Int.LtNeg_0.of.Gt_0
import Lemma.Int.Mul_Neg.eq.NegSquare
import Lemma.Nat.Mul
import Lemma.Rat.Div.gt.Zero.of.Gt_0.Gt_0
import Lemma.Rat.Div.gt.Zero.of.Lt_0.Lt_0
open Hyperreal Int Rat Nat
set_option maxHeartbeats 2000000


@[main]
private lemma main
  {b y : ℝ*}
-- given
  (h_infty : b → ∞)
  (h_or : b = -y ∨ stdPart (b / y) = -1) :
-- imply
  b * y < 0 := by
-- proof
  obtain h_by | h_st := h_or
  ·
    have hy : y = -b := by linarith
    rw [hy, Mul_Neg.eq.NegSquare]
    have hb0 := Ne_0.of.Infinite h_infty
    have h_sq := GtSquare_0.of.Ne_0 hb0
    exact LtNeg_0.of.Gt_0 h_sq
  ·
    if h_y0 : y = 0 then
      rw [h_y0] at h_st
      norm_num at h_st
    else
      have h_eps : (b / y + 1) → 0 := by
        have h_fin : ¬(b / y) → ∞ := fun h_inf => by
          have := EqSt_0.of.Infinite h_inf
          rw [h_st] at this
          norm_num at this
        simpa using InfinitesimalSub.of.EqSt.NotInfinite h_fin h_st
      obtain h_b_pos | h_b_neg := InfinitePos.ou.InfiniteNeg.of.Infinite h_infty
      ·
        rw [InfinitePos.is.Infinite.Gt_0] at h_b_pos
        have hb_gt : b > 0 := h_b_pos.right
        have h_y_neg : y < 0 := by
          by_contra h_not
          have h_ge : 0 ≤ y := not_lt.mp h_not
          obtain h_eq | h_pos := eq_or_lt_of_le h_ge
          · exact h_y0 h_eq.symm
          ·
            have h_div_pos := Div.gt.Zero.of.Gt_0.Gt_0 hb_gt h_pos
            exact absurd h_eps (NotInfinitesimalAdd.of.Ge_0.Gt_0 (le_of_lt h_div_pos) (by norm_num))
        rw [Mul.comm]
        exact Gt0Mul.of.Lt_0.Gt_0 h_y_neg hb_gt
      ·
        rw [InfiniteNeg.is.Infinite.Lt_0] at h_b_neg
        have hb_lt : b < 0 := h_b_neg.right
        have h_y_pos : y > 0 := by
          by_contra h_not
          have h_nonpos : y ≤ 0 := le_of_not_gt h_not
          obtain h_eq | h_neg := eq_or_lt_of_le h_nonpos
          · exact h_y0 h_eq
          ·
            have h_div_pos := Div.gt.Zero.of.Lt_0.Lt_0 hb_lt h_neg
            exact absurd h_eps (NotInfinitesimalAdd.of.Ge_0.Gt_0 (le_of_lt h_div_pos) (by norm_num))
        exact Gt0Mul.of.Lt_0.Gt_0 hb_lt h_y_pos


-- created on 2026-07-26
