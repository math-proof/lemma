import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.List.ProdEraseIdx.eq.Mul_ProdDrop_2.of.GtLength_0
import Lemma.List.TakeEraseIdx.eq.EraseIdxTake.of.Le
import Lemma.Nat.EqMulS.of.Eq
open List Nat


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_s : s.length > 0) 
  (d : ℕ):
-- imply
  ((s.eraseIdx 1).take (d + 1)).prod = s[0] * ((s.drop 2).take d).prod := by
-- proof
  rw [TakeEraseIdx.eq.EraseIdxTake.of.Le]
  ·
    rw [ProdEraseIdx.eq.Mul_ProdDrop_2.of.GtLength_0]
    ·
      rw [GetTake.eq.Get.of.Lt_LengthTake]
      apply EqMulS.of.Eq.left
      apply congrArg
      rw [DropTake.eq.TakeDrop]
      simp
    ·
      simpa
  ·
    omega


-- created on 2025-11-04
