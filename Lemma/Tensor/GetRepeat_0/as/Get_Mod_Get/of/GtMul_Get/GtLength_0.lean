import sympy.tensor.tensor
import Lemma.Tensor.LengthRepeat.eq.Mul_Get_0.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Vector.GetFlatten_AddMul.eq.Get.of.Lt.Lt
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.EqGetSplitAt_0'0
import Lemma.Vector.Get
import Lemma.Vector.GetRepeat.eq.Get_Mod.of.Lt_Mul
import Lemma.Nat.ModAddMul.eq.Mod
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.List.EqProdTakeSet__1.of.GtLength_0
import Lemma.List.AddMul_ProdTail.lt.Mul_Prod.of.Lt_ProdTailSet.Lt.GtGet_0.GtLength_0
import Lemma.List.ProdSet__MulGet.eq.Mul_Prod.of.GtLength
open Tensor Vector List Bool Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0 |
| fin | Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0.fin |
| cast | Tensor.GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0 |
| cast.fin | Tensor.GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0.fin |
-/
@[main, fin, cast, cast.fin]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : n * s[0] > i)
  (X : Tensor α s) :
-- imply
  have h_i : i < (X.repeat ⟨0, h_s⟩ n).length := by rwa [LengthRepeat.eq.Mul_Get_0.of.GtLength_0]
  have h_mod : i % s[0] < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h_s]
    apply LtMod.of.Gt_0 ∘ Gt_0.of.GtMul
    assumption
  (X.repeat ⟨0, h_s⟩ n)[i] ≃ X[i % s[0]] := by
-- proof
  intros
  obtain ⟨q, r, h_qr⟩ := Fin.Any_Eq_AddMul.of.Lt_Mul h_i
  simp [h_qr, EqMod]
  unfold Tensor.repeat
  simp
  simp only [GetElem.getElem]
  unfold Tensor.get
  unfold Tensor.toVector
  simp
  repeat rw [GetCast_Map.eq.UFnGet.of.Eq.Lt]
  ·
    apply SEq.of.SEqDataS.Eq
    ·
      apply TailSet_0.eq.Tail
    ·
      simp
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
      ·
        simp
      ·
        match X with
        | ⟨data⟩ =>
          simp
          apply SEq.of.All_EqGetS.Eq
          ·
            intro k
            have h_k := k.isLt
            simp at h_k
            have h_lt_add := AddMul_ProdTail.lt.Mul_Prod.of.Lt_ProdTailSet.Lt.GtGet_0.GtLength_0 h_s (r.isLt) (q.isLt) h_k
            simp only [GetElem.getElem]
            rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop.fin]
            have := GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop.fin
              (s := s) (d := 1) (i := r) (j := k)
              (by simp_all) (by simp_all [TailSet_0.eq.Tail]) data
            simp [this]
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              simp [TailSet_0.eq.Tail]
              simp [show (q * s[0] + r) * s.tail.prod + k = 0 * (n * s.prod) + (q * s[0] + r) * s.tail.prod + k by simp]
              simp only [AddAdd.eq.Add_Add]
              rw [GetFlatten_AddMul.eq.Get.of.Lt.Lt.fin (by grind)]
              ·
                rw [GetMap.eq.UFnGet.of.Lt.fin (by simp)]
                simp only [GetElem.getElem]
                conv_lhs => erw [EqGetSplitAt_0'0.fin data]
                conv_lhs => rw [Get]
                simp [GetRepeat.eq.Get_Mod.of.Lt_Mul h_lt_add]
                simp [Get]
                congr
                rw [MulAdd.eq.AddMulS]
                rw [MulMul.eq.Mul_Mul]
                have h_prod := Prod.eq.Mul_ProdTail.of.GtLength_0 h_s
                rw [← h_prod]
                rw [AddAdd.eq.Add_Add]
                rw [ModAddMul.eq.Mod]
                apply EqMod.of.Lt
                have := AddMul.lt.Mul.of.Lt.Lt (r.isLt) h_k
                rw [TailSet_0.eq.Tail] at this
                convert this
              ·
                assumption
            ·
              simp [ProdSet__MulGet.eq.Mul_Prod.of.GtLength h_s n]
          ·
            simp [TailSet_0.eq.Tail]
  ·
    simp_all
  ·
    apply ProdTake_1.eq.HeadD_1
  ·
    convert AddMul.lt.Mul q r
    apply EqProdTakeSet__1.of.GtLength_0 h_s
  ·
    rw [EqProdTakeSet__1.of.GtLength_0 h_s]
    rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
    rw [EqGetSet.of.GtLength h_s]


-- created on 2025-07-10
-- updated on 2025-07-18
