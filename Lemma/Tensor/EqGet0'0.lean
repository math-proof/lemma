import sympy.tensor.tensor
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Nat.LtVal
import Lemma.Tensor.ProdTake_1.eq.Length.of.GtLength
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Tensor.Length.eq.HeadD.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.GetSplitAt_1.eq.Cast_GetUnflatten
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
import Lemma.Vector.EqGet0'0
open Tensor Nat Vector Bool List


@[main]
private lemma fin
  [Zero α]
-- given
  (i : Fin (0 : Tensor α s).length) :
-- imply
  (0 : Tensor α s).get i = 0 := by
-- proof
  simp [Tensor.get]
  simp [Tensor.toVector]
  have h_i := LtVal i
  have h_i := ProdTake_1.eq.Length.of.GtLength h_i
  simp [GetElem.getElem]
  rw [GetCast.eq.Get.of.Eq.fin]
  ·
    rw [GetMap.eq.UFnGet.of.Lt.fin]
    apply Eq.of.EqDataS
    simp [EqData0'0]
    apply EqCast.of.SEq
    rw [GetSplitAt_1.eq.Cast_GetUnflatten.fin (0 : List.Vector α s.prod) ⟨i, by simp_all⟩]
    apply SEq.of.All_EqGetS.Eq.fin (by simp)
    intro j
    have h_j := LtVal j
    simp at h_j
    simp [EqGet0'0.fin ⟨j, h_j⟩ (α := α)]
    have h_eq := Prod.eq.MulProdTake__ProdDrop s 1
    rw [GetUnflatten.eq.Get_AddMul.fin (cast (congrArg (List.Vector α) h_eq) (0 : List.Vector α s.prod)) ⟨i, by simp_all⟩ j]
    rw [GetCast.eq.Get.of.Eq.fin h_eq]
    simp [EqGet0'0.fin]
  ·
    rw [h_i]
    apply Length.eq.HeadD.of.GtLength_0 (by omega)


@[main]
private lemma main
  [Zero α]
-- given
  (i : Fin (0 : Tensor α s).length) :
-- imply
  (0 : Tensor α s)[i.val] = 0 := by
-- proof
  apply fin


-- created on 2025-10-12
