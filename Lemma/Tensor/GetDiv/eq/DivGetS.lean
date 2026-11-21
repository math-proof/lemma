import Instance.Data.Tensor.Tensor
import Lemma.Tensor.LengthDiv.eq.Length
import Lemma.Tensor.Length
import Theorem.Tensor.Eq.is.EqDataS
import Theorem.List.ProdTake_1.eq.HeadD_1
import Lemma.Vector.DivCastS.as.Div.of.Eq
import Lemma.Vector.SplitAtDiv.eq.DivSplitAtS
open Tensor Vector List


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.GetDiv.eq.DivGetS |
| fin | Tensor.GetDiv.eq.DivGetS.fin |
-/
@[path, fin]
private lemma main
  [Div α]
-- given
  (A B : Tensor α s)
  (i : Fin A.length) :
-- imply
  (A / B)[i]'(by simp [LengthDiv.eq.Length.left A B]) = A[i] / B[i]'(by simp [Length B A]) := by
-- proof
  simp [GetElem.getElem]
  simp [HDiv.hDiv]
  apply Eq.of.EqDataS
  simp [Tensor.get]
  simp [Tensor.toVector]
  simp [GetElem.getElem]
  repeat rw [GetCast.eq.Get.of.Eq.fin (by simp [ProdTake_1.eq.HeadD_1])]
  simp [Div.div]
  rw [DivCastS.eq.Cast_Div.of.Eq (by simp)]
  congr
  rw [SplitAtDiv.eq.DivSplitAtS]
  rw [GetDiv.eq.DivGetS.fin]


-- created on 2025-10-08
-- updated on 2026-11-21
