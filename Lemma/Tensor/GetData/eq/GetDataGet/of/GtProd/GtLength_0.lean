import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.GtProdTail_0.of.GtProd_0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetSplitAt_1.eq.Cast_GetUnflatten
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
open Vector List Tensor Nat


@[main, fin]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : s.prod > i)
  (X : Tensor α s) :
-- imply
  have h_prod := Prod.eq.Mul_ProdTail.of.GtLength_0 h_s
  have h_i_div : i / s.tail.prod < s[0] := by
    rw [h_prod] at h_i
    apply LtDiv.of.Lt_Mul h_i
  have h_i_div : i / s.tail.prod < X.length := by
    rwa [← Length.eq.Get_0.of.GtLength_0 h_s X] at h_i_div
  have h_pos : s.tail.prod > 0 := GtProdTail_0.of.GtProd_0 (by grind)
  have h_i_mod := LtMod.of.Gt_0 h_pos i
  X.data[i]'(by simpa) = X[i / s.tail.prod].data[i % s.tail.prod] := by
-- proof
  intro h_prod
  simp [GetElem.getElem]
  simp [Tensor.get]
  unfold Tensor.toVector
  simp [GetElem.getElem]
  rw [GetCast.eq.Get.of.Eq.fin]
  .
    simp
    rw [GetSplitAt_1.eq.Cast_GetUnflatten.fin]
    rw [GetCast.eq.Get.of.Eq.fin]
    .
      rw [GetUnflatten.eq.Get_AddMul.fin]
      rw [GetCast.eq.Get.of.Eq.fin]
      .
        have := EqAddMulDiv i s.tail.prod
        grind
      .
        simpa [ProdTake_1.eq.Get_0.of.GtLength_0 h_s]
    .
      simp
  .
    apply ProdTake_1.eq.HeadD_1


-- created on 2026-04-08
