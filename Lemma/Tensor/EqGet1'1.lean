import sympy.tensor.tensor
import Lemma.Tensor.ProdTake_1.eq.Length.of.GtLength
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Tensor.Length.eq.HeadD.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData1'1
import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.GetSplitAt_1.eq.Cast_GetUnflatten
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.List.Prod.eq.MulProdS
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.EqGet1'1
open Tensor Vector Bool List


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
  have h_i := i.isLt
  have h_i := ProdTake_1.eq.Length.of.GtLength h_i
  simp [GetElem.getElem]
  rw [GetCast.eq.Get.of.Eq.fin]
  ·
    rw [GetMap.eq.UFnGet.of.Lt.fin (by grind)]
    apply Eq.of.EqDataS
    simp [EqData1'1]
    apply EqCast.of.SEq
    simp [GetSplitAt_1.eq.Cast_GetUnflatten.fin (1 : List.Vector α s.prod) ⟨i, by simp_all⟩]
    apply SEq.of.All_EqGetS.Eq.fin (by simp)
    intro j
    have h_j := j.isLt
    simp at h_j
    simp [EqGet1'1.fin ⟨j, h_j⟩ (α := α)]
    have h_eq := Prod.eq.MulProdS s 1
    simp [GetUnflatten.eq.Get_AddMul.fin (cast (congrArg (List.Vector α) h_eq) (1 : List.Vector α s.prod)) ⟨i, by simp_all⟩ j]
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
