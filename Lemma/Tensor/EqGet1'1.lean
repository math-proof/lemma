import sympy.tensor.tensor
import Lemma.Tensor.GetCast.eq.Get.of.Eq.Lt
import Lemma.Nat.LtVal
import Lemma.Tensor.ProdTake_1.eq.Length.of.GtLength
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Tensor.Length.eq.HeadD.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData1'1
import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.GetSplitAt_1.eq.Cast_GetUnflatten
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.EqGet1'1
open Tensor Nat Vector Bool List


@[main]
private lemma fin
  [One α]
-- given
  (i : Fin (1 : Tensor α s).length) :
-- imply
  (1 : Tensor α s).get i = 1 := by
-- proof
  simp [Tensor.get]
  simp [Tensor.toVector]
  have h_i := LtVal i
  have h_i := ProdTake_1.eq.Length.of.GtLength h_i
  rw [GetCast.eq.Get.of.Eq.Lt (by grind)]
  ·
    rw [GetMap.eq.UFnGet.of.Lt (by grind)]
    apply Eq.of.EqDataS
    simp [EqData1'1]
    apply EqCast.of.SEq
    have := GetSplitAt_1.eq.Cast_GetUnflatten (1 : List.Vector α s.prod) ⟨i, by simp_all⟩
    simp at this
    simp [this]
    apply SEq.of.All_EqGetS.Eq (by simp)
    intro j
    have h_j := LtVal j
    simp at h_j
    have := EqGet1'1 ⟨j, h_j⟩ (α := α)
    simp at this
    simp [this]
    have h_eq := Prod.eq.MulProdTake__ProdDrop s 1
    have := GetUnflatten.eq.Get_AddMul (cast (congrArg (List.Vector α) h_eq) (1 : List.Vector α s.prod)) ⟨i, by simp_all⟩ j
    simp at this
    simp [this]
    simp only [GetElem.getElem]
    rw [GetCast.eq.Get.of.Eq.fin h_eq]
    simp [EqGet1'1.fin]
  ·
    rw [h_i]
    apply Length.eq.HeadD.of.GtLength_0 (by omega)


@[main]
private lemma main
  [One α]
-- given
  (i : Fin (1 : Tensor α s).length) :
-- imply
  (1 : Tensor α s)[i.val] = 1 := by
-- proof
  apply fin


-- created on 2025-10-12
