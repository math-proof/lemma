import sympy.tensor.tensor
import Lemma.Tensor.LengthRepeat.eq.Mul_Get_0.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Gt_0.of.GtMul
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqMod
import Lemma.Nat.LtVal
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.List.TailSet_0.eq.Tail
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Vector.GetFlatten_AddMul.eq.Get.of.Lt.Lt
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.EqGetSplitAt_0'0
import Lemma.Vector.EqGetS
import Lemma.Vector.GetRepeat.eq.Get_Mod.of.Lt_Mul
import Lemma.Nat.Gt_0
import Lemma.List.GtProd_0.of.Get_0.gt.Zero.ProdTail.gt.Zero.GtLength_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.ModAddMul.eq.Mod
import Lemma.Nat.EqMod.of.Lt
import Lemma.Vector.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.List.EqProdTakeSet__1.of.GtLength_0
import Lemma.List.AddMul_ProdTail.lt.Mul_Prod.of.Lt_ProdTailSet.Lt.Lt_Get_0.GtLength_0
import Lemma.List.ProdSet__MulGet.eq.Mul_Prod.of.Lt_Length
import Lemma.List.GtProdTail_0.of.Lt_ProdTailSet_0
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.List.EqGetSet.of.Lt_Length
open Tensor Vector List Bool Nat


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : i < n * s[0])
  (X : Tensor α s) :
-- imply
  have h_i : i < (X.repeat n ⟨0, h_s⟩).length := by rwa [LengthRepeat.eq.Mul_Get_0.of.GtLength_0]
  have h_mod : i % s[0] < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h_s]
    apply LtMod.of.Gt_0 ∘ Gt_0.of.GtMul
    assumption
  (X.repeat n ⟨0, h_s⟩)[i] ≃ X[i % s[0]] := by
-- proof
  intros
  obtain ⟨j, i, h_ij⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_i
  simp [h_ij, EqMod]
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
            have h_k := LtVal k
            simp at h_k
            have h_lt_add := AddMul_ProdTail.lt.Mul_Prod.of.Lt_ProdTailSet.Lt.Lt_Get_0.GtLength_0 h_s (LtVal i) (LtVal j) h_k
            simp only [GetElem.getElem]
            rw [GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop.fin]
            have := GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop.fin
              (s := s) (d := 1) (i := i) (j := k)
              (by simp_all) (by simp_all [TailSet_0.eq.Tail]) data
            simp [this]
            rw [GetCast.eq.Get.of.Eq.Lt.fin]
            ·
              simp [TailSet_0.eq.Tail]
              simp [show (j * s[0] + i) * s.tail.prod + k = 0 * (n * s.prod) + (j * s[0] + i) * s.tail.prod + k by simp]
              simp only [AddAdd.eq.Add_Add]
              rw [GetFlatten_AddMul.eq.Get.of.Lt.Lt.fin (by grind)]
              ·
                rw [GetMap.eq.UFnGet.of.Lt.fin (by simp)]
                simp only [GetElem.getElem]
                rw [EqGetSplitAt_0'0.fin data]
                repeat rw [EqGetS]
                simp
                rw [GetRepeat.eq.Get_Mod.of.Lt_Mul]
                congr
                rw [MulAdd.eq.AddMulS]
                rw [MulMul.eq.Mul_Mul]
                have h_prod := Prod.eq.Mul_ProdTail.of.GtLength_0 h_s
                rw [← h_prod]
                rw [AddAdd.eq.Add_Add]
                rw [ModAddMul.eq.Mod]
                apply EqMod.of.Lt
                have := AddMul.lt.Mul.of.Lt.Lt (LtVal i) h_k
                simp at this
                rw [TailSet_0.eq.Tail] at this
                convert this
              ·
                assumption
            ·
              simpa [TailSet_0.eq.Tail]
            ·
              simp [ProdSet__MulGet.eq.Mul_Prod.of.Lt_Length h_s n]
          ·
            simp [TailSet_0.eq.Tail]
  ·
    simp_all
  ·
    apply ProdTake_1.eq.HeadD_1
  ·
    convert AddMul.lt.Mul j i
    apply EqProdTakeSet__1.of.GtLength_0 h_s
  ·
    rw [EqProdTakeSet__1.of.GtLength_0 h_s]
    rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
    rw [EqGetSet.of.Lt_Length h_s]


@[main]
private lemma fin
-- given
  (h_s : s.length > 0)
  (h_i : i < n * s[0])
  (X : Tensor α s) :
-- imply
  have h_i : i < (X.repeat n ⟨0, h_s⟩).length := by rwa [LengthRepeat.eq.Mul_Get_0.of.GtLength_0]
  have h_mod : i % s[0] < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h_s]
    apply LtMod.of.Gt_0 ∘ Gt_0.of.GtMul
    assumption
  (X.repeat n ⟨0, h_s⟩).get ⟨i, h_i⟩ ≃ X.get ⟨i % s[0], h_mod⟩ := by
-- proof
  apply main
  assumption


-- created on 2025-07-10
-- updated on 2025-07-18
