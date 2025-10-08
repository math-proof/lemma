import sympy.tensor.functions
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.Nat.Gt_0
import Lemma.Tensor.ProdTake_1.eq.Length.of.GtLength_0
import Lemma.Vector.GetSplitAt_1.eq.Cast_GetUnflatten
import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Tensor.LengthInv.eq.Length
open Tensor Vector List Nat Bool


@[main]
private lemma fin
  [Inv α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  (X⁻¹).get ⟨i, by simp [LengthInv.eq.Length]⟩ = (X.get i)⁻¹ := by
-- proof
  simp [Inv.inv]
  apply Eq.of.EqDataS
  simp [Tensor.get]
  simp [Tensor.toVector]
  have h_take_1 := ProdTake_1.eq.HeadD_1 s
  have h_length := ProdTake_1.eq.Length.of.GtLength_0 (Gt_0 i)
  rw [GetCast_Map.eq.UFnGet.of.Eq.Lt (by simp [h_length]) h_take_1]
  simp only [GetElem.getElem]
  rw [GetSplitAt_1.eq.Cast_GetUnflatten.fin]
  apply EqCast.of.SEq
  apply SEq.of.All_EqGetS.Eq (by simp)
  intro j
  simp only [GetElem.getElem]
  simp [GetUnflatten.eq.Get_AddMul.fin]
  have h_s := Prod.eq.MulProdTake__ProdDrop s 1
  rw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin _ h_s]
  apply congrArg
  rw [GetCast_Map.eq.UFnGet.of.Eq.Lt.fin (by simp [h_length]) h_take_1]
  simp
  rw [GetSplitAt_1.eq.Cast_GetUnflatten.fin]
  rw [GetCast.eq.Get.of.Eq.fin (by simp)]
  simp [GetUnflatten.eq.Get_AddMul.fin]
  rw [GetCast.eq.Get.of.Eq.fin h_s]


@[main]
private lemma main
  [Inv α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  have hi : i < X⁻¹.length := by simp [LengthInv.eq.Length]
  X⁻¹[i] = X[i]⁻¹ := by
-- proof
  apply fin


-- created on 2025-10-08
