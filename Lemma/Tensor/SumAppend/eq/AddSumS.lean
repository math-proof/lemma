import Lemma.Bool.HEq.of.SEq
import Lemma.List.TakeCons.eq.Cons_Take
import Lemma.Nat.AddMul.lt.Mul.of.Lt
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Tensor.DataSum_0.eq.SumSplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SumAppend.eq.AddSumS
open Bool List Nat Tensor Vector


@[main]
private lemma main
  [AddMonoid α]
-- given
  (A : Tensor α (n :: s))
  (B : Tensor α (m :: s)) :
-- imply
  let lhs : Tensor α s := A.sum 0
  let rhs : Tensor α s := B.sum 0
  (A ++ B).sum 0 = lhs + rhs := by
-- proof
  apply Eq.of.EqDataS
  erw [DataAdd.eq.AddDataS]
  simp [DataSum_0.eq.SumSplitAtData]
  rw [DataAppend.eq.Cast_AppendDataS]
  erw [AddSumS.eq.SumAppend]
  congr 1
  ·
    simp
  ·
    apply HEq.of.SEq
    apply SEq.of.All_EqGetS.Eq.fin (by simp)
    intro i
    have h_i := i.isLt
    ext j
    rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    rw [GetCast.eq.Get.of.Eq.fin (by grind)]
    simp
    if h_in : i < n then
      erw [GetAppend.eq.Get.of.Lt.fin (AddMul.lt.Mul.of.Lt.Lt h_in j.isLt)]
      erw [GetAppend.eq.Get.of.Lt.fin (by simpa using h_in)]
      erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      simp
    else
      have hn : n ≤ i := by omega
      have h_ge := Nat.le_trans (Nat.mul_le_mul_right s.prod hn) (Nat.le_add_right _ j)
      have h_lt : i * s.prod + j < n * s.prod + (m :: s).prod := by
        apply lt_of_lt_of_eq (AddMul.lt.Mul.of.Lt (by simpa [TakeCons.eq.Cons_Take] using h_i) j)
        exact Nat.add_mul n m s.prod
      erw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin h_ge h_lt]
      erw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by simp; omega)]
      erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      simp
      congr 1
      simp
      have h_le := Nat.mul_le_mul_right s.prod hn
      calc
        _ = j + (↑i * s.prod - n * s.prod) := by grind
        _ = (i - n) * s.prod + j := by grind


-- created on 2026-07-22
