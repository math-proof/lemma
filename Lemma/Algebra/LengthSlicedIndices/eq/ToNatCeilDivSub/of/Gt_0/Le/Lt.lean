import Lemma.Algebra.GeCeil
import Lemma.Algebra.LeMulS.of.Le.Gt_0
import Lemma.Algebra.GtCoeS.is.Gt
import Lemma.Algebra.EqMulDiv.of.Gt_0
import Lemma.Algebra.Sub.gt.Zero.is.Gt
import Lemma.Algebra.CoeSub.eq.SubCoeS.of.Gt
import Lemma.Algebra.GtDivS.of.Gt.Gt_0
import Lemma.Algebra.Gt.of.Ge.Gt
import Lemma.Algebra.GtCoeS.is.Gt
import Lemma.Algebra.Eq_ToNat.of.Gt_0
import Lemma.Algebra.CoeSub.eq.SubCoeS.of.Gt
import Lemma.Algebra.LengthSlicedIndices.eq.CeilDivSub.of.Gt_0.Le.Lt.Sub.le.Mul
import Lemma.Algebra.EqCoeS.is.Eq
open Algebra


@[main]
private lemma main
-- given
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (h_step : step > 0) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step).length = ⌈(stop - start : ℚ) / step⌉.toNat := by
-- proof
  have h_Gt_0 := Sub.gt.Zero.of.Gt.nat h_start
  have h_Gt_0 := GtCoeS.of.Gt.nat (R := ℚ) h_Gt_0
  rw [CoeSub.eq.SubCoeS.of.Gt h_start] at h_Gt_0
  have h_step' := GtCoeS.of.Gt.nat (R := ℚ) h_step
  have h_Gt_0 := GtDivS.of.Gt.Gt_0 h_Gt_0 h_step'
  simp at h_Gt_0
  have h_Le := GeCeil (x := (stop - start : ℚ) / step)
  have h_Gt_0 := Gt.of.Ge.Gt h_Le h_Gt_0
  have h_Gt_0 := Gt.of.GtCoeS.int h_Gt_0
  have h_Eq := Eq_ToNat.of.Gt_0 h_Gt_0
  apply Eq.of.EqCoeS.nat (R := ℤ)
  rw [← h_Eq]
  have h_Le := LeMulS.of.Le.Gt_0 h_Le h_step'
  rw [EqMulDiv.of.Gt_0 h_step'] at h_Le
  rw [h_Eq] at h_Le
  rw [SubCoeS.eq.CoeSub.of.Gt h_start] at h_Le
  have h_Le : stop - start ≤ ⌈((stop - start : ℕ) : ℚ) / step⌉.toNat * step := by
    norm_cast
    norm_cast at h_Le
  apply LengthSlicedIndices.eq.CeilDivSub.of.Gt_0.Le.Lt.Sub.le.Mul h_Le h_start h_stop h_step


-- created on 2025-05-04
-- updated on 2025-05-05
