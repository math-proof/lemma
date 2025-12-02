import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.DropTail.eq.Drop
import Lemma.List.EqAppendTake__Drop
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdDrop.dvd.ProdTail.of.Gt_0
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.ProdTail.eq.MulProdTailTake.of.Gt_0
import Lemma.List.Rotate.eq.AppendDrop__Take
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TailTake.eq.TakeTail
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.DivAddMul.eq.Add_Div.of.Gt_0
import Lemma.Nat.Dvd_Mul.of.Dvd
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.ModAdd.eq.Mod.of.Dvd
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Tensor.DataGet.eq.Cast_GetSplitAtData.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermuteTail.eq.Get_0.of.GtLength
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector


@[main]
private lemma main
  {s : List ℕ}
  {k : ℕ}
-- given
  (h_d : s.length > d)
  (h_k : k < s[0])
  (X : Tensor α s) :
-- imply
  (X.permuteTail d).get ⟨k, by rwa [LengthPermuteTail.eq.Get_0.of.GtLength h_d]⟩ ≃ (X.get ⟨k, by rwa [Length.eq.Get_0.of.GtLength_0 (by omega)]⟩).permuteTail d := by
-- proof
  unfold permuteTail
  simp
  apply SEq.of.SEqDataS.Eq
  ·
    rw [TailAppend.eq.AppendTail.of.GtLength_0]
    ·
      rw [← TailTake.eq.TakeTail]
      simp [show (s.length - 1 - d + 1) = s.length - d by omega]
      simp [show (d ⊓ (s.length - 1) - 1) = (d ⊓ s.length - 1) by omega]
    ·
      simp
      omega
  ·
    simp
    rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, ?_⟩)]
    ·
      apply SEqCastS.of.SEq.Eq.Eq
      ·
        simp
      ·
        rw [MulProdS.eq.ProdAppend]
      ·
        simp
        apply SEq.of.All_EqGetS.Eq
        ·
          intro t
          have h_t := t.isLt
          simp only [GetElem.getElem]
          rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp [GetCast.eq.Get.of.Eq.fin]
          simp at h_t
          simp [TailAppend.eq.AppendTail.of.GtLength_0 (show (s.take (s.length - d)).length > 0 by simp; omega)] at h_t ⊢
          simp [ProdRotate.eq.Prod] at h_t ⊢
          simp [MulProdTailTake.eq.ProdTail.of.Gt_0 (show (s.length - d) > 0 by omega)] at h_t ⊢
          have h_lt : t < (s.tail.take (s.tail.length - d)).prod * ((s.tail.drop (s.tail.length - d)).rotate (d ⊓ s.tail.length - 1)).prod := by 
            simp [ProdRotate.eq.Prod]
            simp only [Drop.eq.DropTail]
            rw [MulProdS.eq.ProdAppend]
            rwa [EqAppendTake__Drop]
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          have h_q := q.isLt
          have h_r := r.isLt
          let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
          have h_lt : k * s.tail.prod + ↑t < (s.take (s.length - d)).prod * ((s.drop (s.length - d)).rotate (d ⊓ s.length - 1)).prod := by 
            simp [ProdRotate.eq.Prod]
            conv_rhs => rw [Prod.eq.Mul_ProdTail.of.GtLength_0 (by omega)]
            exact AddMul.lt.Mul.of.Lt.Lt h_k h_t
          let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
          have h_q' := q'.isLt
          have h_r' := r'.isLt
          simp only [Rotate.eq.AppendDrop__Take, ProdAppend.eq.MulProdS] at h_r' h_r
          let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          unfold Tensor.rotate
          simp
          repeat rw [GetCast.eq.Get.of.Eq.fin]
          let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r
          let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
          have h_qₐ := qₐ.isLt
          have h_rₐ := rₐ.isLt
          simp at h_qₐ h_rₐ
          let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r'
          let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
          have h_qₑ := qₑ.isLt
          have h_rₑ := rₑ.isLt
          repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
          repeat rw [GetTranspose.eq.Get.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp
          rw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (i := ⟨k, ?_⟩)]
          ·
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              apply congrArg
              simp [ProdRotate.eq.Prod] at *
              rw [ModAdd.eq.Mod.of.Dvd.left] at h_r'_mod
              ·
                simp [show d ⊓ s.length = d by omega] at *
                simp [show (s.length - 1 - d + 1) = s.length - d by omega] at *
                simp [show d ⊓ (s.length - 1) = d by omega] at *
                simp [show s.length - (s.length - d) = d by omega] at *
                rw [ProdTail.eq.MulProdTailTake.of.Gt_0 (by omega) (d := s.length - d)] at h_q'_div
                rw [Mul_Mul.eq.MulMul] at h_q'_div
                rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_q'_div
                simp [h_q'_div, h_q_div]
                rw [MulAdd.eq.AddMulS]
                rw [MulMul.eq.Mul_Mul]
                rw [MulProdTailTake.eq.ProdTail.of.Gt_0 (by omega)]
                simp [AddAdd.eq.Add_Add]
                simp [h_qₐ_div, h_qₑ_div]
                simp [h_rₐ_mod, h_rₑ_mod]
                simp [h_r_mod, h_r'_mod]
              ·
                apply Dvd_Mul.of.Dvd
                apply ProdDrop.dvd.ProdTail.of.Gt_0
                omega
            ·
              simp
          ·
            omega
          ·
            simpa
          ·
            rw [Rotate.eq.AppendDrop__Take]
            rw [ProdAppend.eq.MulProdS]
          ·
            rw [Rotate.eq.AppendDrop__Take]
            rw [ProdAppend.eq.MulProdS]
        ·
          simp [TailAppend.eq.AppendTail.of.GtLength_0 (show (s.take (s.length - d)).length > 0 by simp; omega)]
          simp [ProdRotate.eq.Prod]
          simp [MulProdTailTake.eq.ProdTail.of.Gt_0 (show (s.length - d) > 0 by omega)]
          simp only [Drop.eq.DropTail]
          rw [MulProdS.eq.ProdAppend]
          rw [EqAppendTake__Drop]
    ·
      simp
      omega
    ·
      rw [GetAppend.eq.Get.of.GtLength]
      ·
        rwa [GetTake.eq.Get.of.Lt_LengthTake]
      ·
        simp
        omega


-- created on 2025-12-02
