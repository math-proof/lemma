import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.DropTail.eq.Drop
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.ProdTake.eq.Mul_ProdTakeTail.of.GtLength_0
import Lemma.List.ProdTake.eq.Mul_ProdTakeTail.of.Gt_0.GtLength_0
import Lemma.List.Set.eq.Cons_Set.of.GtLength_0
import Lemma.List.TailSet.eq.SetTail.of.Gt_0
import Lemma.Nat.EqSubAdd
import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import Lemma.Tensor.DataResize.as.FlattenMapSplitAtData
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.Length.eq.Get_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Lt_Mul
import Lemma.Vector.GetResize.eq.Ite_Get_Mod
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
  {i : Fin s.length}
-- given
  (X : Tensor α s)
  (h_i : i.val > 0)
  (n : ℕ) :
-- imply
  X.resize i n ≃ Tensor.fromVector (X.toVector.map (·.resize ⟨i - 1, by grind⟩ n)) := by
-- proof
  match h_match : i with
  | ⟨0, h_i⟩ =>
    nomatch h_i
  | ⟨j + 1, h_i⟩ =>
    conv_lhs => unfold Tensor.resize
    simp
    apply SEq.of.SEqDataS.Eq
    ·
      rw [Set.eq.Cons_Set.of.GtLength_0 (by grind)]
      congr 1
      rw [HeadD.eq.Get_0.of.GtLength_0]
    ·
      simp
      apply SEqCast.of.SEq.Eq
      ·
        rwa [ProdSet.eq.MulProd_Mul_Prod.of.GtLength]
      ·
        rw [DataFromVector.eq.FlattenMapData]
        apply SEq.of.All_EqGetS.Eq.fin
        ·
          intro t
          have h_t := t.isLt
          repeat rw [GetFlatten.eq.Get.of.Lt_Mul]
          ·
            simp
            have h_Xs := Length.eq.Get_0.list X i
            have h_t : t / (s.set (j + 1) n).tail.prod < s[0] := by
              apply LtDiv.of.Lt_Mul
              simp [ProdTake.eq.Mul_ProdTakeTail.of.GtLength_0 (by grind) j (s := s)] at h_t
              rw [MulMul.eq.Mul_Mul] at h_t
              convert h_t
              rw [TailSet.eq.SetTail.of.Gt_0 (by grind)]
              rw [EqSubAdd]
              rw [Drop.eq.DropTail]
              rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by grind)]
            rw [GetToVector.eq.Get.fin (i := ⟨t / (s.set (j + 1) n).tail.prod, by grind⟩)]
            rw [DataResize.eq.Cast_FlattenMapSplitAtData]
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              rw [GetFlatten.eq.Get.of.Lt_Mul]
              ·
                simp [GetResize.eq.Ite_Get_Mod.fin]
                split_ifs with h? h' h''
                ·
                  simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                  rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨t / (s.set (j + 1) n).tail.prod, by grind⟩) (by grind)]
                  rw [GetCast.eq.Get.of.Eq.fin]
                  ·
                    simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                    congr 1
                    simp
                    sorry
                  ·
                    sorry
                ·
                  sorry
                ·
                  sorry
                ·
                  rfl
              ·
                sorry
            ·
              rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by grind)]
              simp
          ·
            rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
            rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by grind)]
            simp [Mul_Mul.eq.MulMul]
            rw [Mul_ProdTakeTail.eq.ProdTake.of.GtLength_0]
            grind
          ·
            grind
        ·
          rw [HeadD.eq.Get_0.of.GtLength_0 (by grind)]
          rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by grind)]
          simp [Mul_Mul.eq.MulMul]
          left
          left
          rw [ProdTake.eq.Mul_ProdTakeTail.of.Gt_0.GtLength_0 (by grind) (by grind)]
          congr 1


-- created on 2026-07-10
-- updated on 2026-07-13
