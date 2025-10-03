import sympy.tensor.tensor
import Lemma.Tensor.LengthRepeat.eq.Mul_Get_0.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Algebra.LtMod.of.Gt_0
import Lemma.Algebra.Gt_0.of.GtMul
import Lemma.Algebra.Any_EqAddMul.of.Lt_Mul
import Lemma.Algebra.EqMod
import Lemma.Algebra.LtVal
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.Algebra.AddMul.lt.Mul
import Lemma.Tensor.SEq.of.SEqDataS.Eq
import Lemma.List.TailSet_0.eq.Tail
import Lemma.Logic.EqCastS.of.Eq.Eq.Eq
import Lemma.Algebra.Eq.of.All_EqGetS.Eq
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop.of.Lt_ProdTake.Lt_ProdDrop
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.Vector.Get.eq.GetFlatten_AddMul.of.Lt.Lt
import Lemma.Algebra.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Algebra.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.EqGetSplitAt_0'0
import Lemma.Algebra.EqGetS
import Lemma.Vector.GetRepeat.eq.Get_Mod.of.Lt_Mul
import Lemma.Algebra.Gt_0
import Lemma.List.GtProd_0.of.Get_0.gt.Zero.ProdTail.gt.Zero.GtLength_0
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Algebra.ModAddMul.eq.Mod
import Lemma.Algebra.EqMod.of.Lt
import Lemma.Algebra.GetCast_Map.eq.UFnGet.of.Eq.Lt
import Lemma.List.EqProdTakeSet__1.of.GtLength_0
import Lemma.List.AddMul_ProdTail.lt.Mul_Prod.of.Lt_ProdTailSet.Lt.Lt_Get_0.GtLength_0
import Lemma.List.ProdSet__MulGet.eq.Mul_Prod.of.Lt_Length
import Lemma.List.GtProdTail_0.of.Lt_ProdTailSet_0
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.List.EqGetSet.of.Lt_Length
open Tensor Algebra Logic Vector List


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : i < n * s[0])
  (X : Tensor α s) :
-- imply
  have : i < (X.repeat n ⟨0, h_s⟩).length := by rwa [LengthRepeat.eq.Mul_Get_0.of.GtLength_0]
  have := Gt_0.of.GtMul h_i
  have : i % s[0] < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h_s]
    apply LtMod.of.Gt_0
    assumption
  (X.repeat n ⟨0, h_s⟩)[i] ≃ X[i % s[0]] := by
-- proof
  intro h_i' h_s_0 h_i_mod
  obtain ⟨j, i, h_ij⟩ := Any_EqAddMul.of.Lt_Mul h_i
  simp [← h_ij]
  simp [EqMod]
  unfold Tensor.repeat
  simp
  simp only [GetElem.getElem]
  simp [Tensor.get]
  unfold Tensor.toVector
  simp
  repeat rw [GetCast_Map.eq.UFnGet.of.Eq.Lt]
  ·
    apply SEq.of.SEqDataS.Eq
    ·
      apply TailSet_0.eq.Tail
    ·
      simp
      apply EqCastS.of.Eq.Eq.Eq
      ·
        simp
      ·
        simp
      ·
        match X with
        | ⟨data⟩ =>
          simp
          apply Eq.of.All_EqGetS.Eq
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
              simp [(show (j * s[0] + i) * s.tail.prod + k = 0 * (n * s.prod) + (j * s[0] + i) * s.tail.prod + k by simp)]
              simp only [AddAdd.eq.Add_Add]
              rw [GetFlatten_AddMul.eq.Get.of.Lt.Lt.fin]
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
    rw [HeadD.eq.Get_0.of.GtLength_0]
    rw [EqGetSet.of.Lt_Length h_s]


-- created on 2025-07-10
-- updated on 2025-07-18
