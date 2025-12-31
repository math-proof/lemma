import Lemma.Tensor.LengthDiv.eq.Length
import sympy.tensor.tensor
import Lemma.Tensor.EqLengthS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.Vector.DivCastS.eq.Cast_Div.of.Eq
import Lemma.Vector.SplitAtDiv.eq.DivSplitAtS
import Lemma.Vector.GetDiv.eq.DivGetS
open Tensor Vector List


@[main]
private lemma main
  [Div α]
-- given
  (A B : Tensor α s)
  (i : Fin A.length) :
-- imply
  (A / B)[i]'(by simp [LengthDiv.eq.Length.left A B]) = A[i] / B[i]'(by simp [EqLengthS B A]) := by
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


@[main]
private lemma fin
  [Div α]
-- given
  (A B : Tensor α s)
  (i : Fin A.length) :
-- imply
  (A / B).get ⟨i, by simp [LengthDiv.eq.Length.left]⟩ = A.get i / B.get ⟨i, by simp [EqLengthS B A]⟩ :=
-- proof
  main A B i


-- created on 2025-10-08
