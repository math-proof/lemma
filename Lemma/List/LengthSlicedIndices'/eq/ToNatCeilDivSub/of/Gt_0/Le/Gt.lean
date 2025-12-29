import Lemma.Nat.Sub.gt.Zero.is.Gt
import Lemma.Int.LtCoeS.is.Lt
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Gt
import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Rat.GeCeil
import Lemma.Nat.Gt.of.Ge.Gt
import Lemma.Int.EqToNat.of.Gt_0
import Lemma.Nat.LeMulS.of.Le.Gt_0
import Lemma.Rat.EqMulDiv.of.Gt_0
import Lemma.Nat.EqCoeS.is.Eq
import Lemma.List.LengthSlicedIndices'.eq.CeilDivSub.of.Gt_0.Le.Gt.Sub.le.Mul
open List Int Nat Rat


@[main]
private lemma main
-- given
  (h_stop : start > stop)
  (h_start : start ≤ n)
  (h_step : step > 0) :
-- imply
  (Nat.sliced_indices' h_stop h_start h_step).length = ⌈(start - stop : ℚ) / step⌉.toNat := by
-- proof
  have h_pos := Sub.gt.Zero.of.Gt h_stop
  have h_pos := GtCoeS.of.Gt (R := ℚ) h_pos
  rw [CoeSub.eq.SubCoeS.of.Gt h_stop] at h_pos
  have h_step' := GtCoeS.of.Gt (R := ℚ) h_step
  have h_pos := GtDivS.of.Gt.Gt_0 h_pos h_step'
  simp at h_pos
  have h_Le := GeCeil (x := (start - stop : ℚ) / step)
  have h_pos := Gt.of.Ge.Gt h_Le h_pos
  have h_pos := Gt.of.GtCoeS h_pos
  have h_Eq := EqToNat.of.Gt_0 h_pos
  apply Eq.of.EqCoeS (R := ℤ)
  rw [h_Eq]
  have h_Le := LeMulS.of.Le.Gt_0 h_Le h_step'
  rw [EqMulDiv.of.Gt_0 h_step'] at h_Le
  rw [← h_Eq] at h_Le
  rw [SubCoeS.eq.CoeSub.of.Gt h_stop] at h_Le
  have h_Le : start - stop ≤ ⌈((start - stop : ℕ) : ℚ) / step⌉.toNat * step := by
    norm_cast at h_Le ⊢
  apply LengthSlicedIndices'.eq.CeilDivSub.of.Gt_0.Le.Gt.Sub.le.Mul h_Le h_stop h_start h_step


-- created on 2025-05-04
-- updated on 2025-05-05
