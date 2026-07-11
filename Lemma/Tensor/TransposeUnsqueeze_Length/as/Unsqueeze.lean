import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.List.EqSwap
import Lemma.List.EqSwap_0'1
import Lemma.List.InsertIdxCons.eq.Cons_InsertIdx.of.Gt_0
import Lemma.List.InsertIdx_Length.eq.Append_List
import Lemma.List.LengthCons.eq.AddLength_1
import Lemma.List.PermuteCons.eq.Cons_Permute.of.Ge
import Lemma.List.PermuteInsertIdx.eq.InsertIdx.of.GtLength_0
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.Permute__Neg1.eq.Swap.of.GtVal_0
import Lemma.List.ProdAppend.eq.MulProdS
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.List.ProdDropCons_Append_List.eq.MulGet.of.GtLength_0
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.List.ProdPermute.eq.Prod
import Lemma.List.ProdRotate.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.Swap.eq.Permute__Neg1.of.GtLength
import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataUnsqueeze.as.Data
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.T.as.Permute__Neg1.of.GtLength_0
import Lemma.Tensor.Unsqueeze.eq.TensorCast_Data
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetTranspose.eq.Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin List Nat Tensor Vector


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α s) :
-- imply
  (X.unsqueeze s.length)ᵀ ≃ X.unsqueeze (s.length - 1) := by
-- proof
  match s with
  | [] =>
    unfold Tensor.T
    unfold Tensor.transpose
    simp
    apply SEqCast.of.Eq
    rw [EqSwap]
  | n :: s =>
    rw [T.eq.Cast_Permute__Neg1.of.GtLength_0 (by simp)]
    simp
    apply SEqCast.of.SEq.Eq
    ·
      simp
      rw [Swap.eq.Permute__Neg1.of.GtLength (by simp)]
      congr 1
      ·
        simp
      ·
        grind
    ·
      rw [@Tensor.Permute.eq.Ite]
      simp
      have h_s := Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
        (s := n :: s.insertIdx s.length 1)
        (i := ⟨(s.insertIdx s.length 1).length, by grind⟩)
        (by grind) 1
      apply SEqCast.of.SEq.Eq (by aesop)
      unfold permuteTail
      simp
      simp only [LengthCons.eq.AddLength_1] at h_s
      apply SEq.of.SEqDataS.Eq
      ·
        rw [← h_s]
        simp
        if h_s : s = [] then
          subst h_s
          simp
          rw [Permute__Neg1.eq.Swap.of.GtVal_0 (by grind)]
          simp [EqSwap_0'1]
        else
          have := PermuteCons.eq.Cons_Permute.of.Ge
            (s := s.insertIdx s.length 1)
            (i := ⟨s.length, by grind⟩)
            (d := 1)
            (by grind)
            n
          simp at this
          rw [this]
          rw [InsertIdxCons.eq.Cons_InsertIdx.of.Gt_0 (by grind)]
          congr 1
          apply PermuteInsertIdx.eq.InsertIdx.of.GtLength_0
          grind
      ·
        simp
        apply SEqCast.of.SEq.Eq (by simp)
        have := DataUnsqueeze.as.Data X s.length
        symm
        apply this.trans
        apply SEq.of.All_EqGetS.Eq.fin (by simp [ProdRotate.eq.Prod])
        intro t
        have h_t := t.isLt
        have h_s := congrArg List.prod h_s
        rw [ProdAppend.eq.MulProdS, ProdPermute.eq.Prod, ProdCons.eq.Mul_Prod, ProdInsertIdx.eq.Prod, Mul_Prod.eq.ProdCons] at h_s
        conv_rhs at h_t => rw [h_s]
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        simp
        unfold Tensor.rotate
        simp
        have h_r := r.isLt
        simp only [ProdRotate.eq.MulProdS] at h_r
        rw [GetCast.eq.Get.of.Eq.fin]
        ·
          let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_r
          let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
          rw [@Vector.GetTranspose.eq.Get.fin]
          repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
          simp [show 1 % (s.length + 1 + 1 - s.length) = 1 by grind]
          simp [Unsqueeze.eq.TensorCast_Data]
          erw [GetCast.eq.Get.of.Eq.fin (by simp)]
          congr 1
          simp
          apply Eq_Fin.of.EqVal
          if h_s : s = [] then
            subst h_s
            simp at h_qr h_q'r' ⊢
            omega
          else
            have h_q' := q'.isLt
            simp [InsertIdx_Length.eq.Append_List s 1] at h_q'
            conv_rhs at h_q' => rw [EqMod.of.Lt (by grind)]
            simp at h_q'
            simp [h_q']
            simp [ProdRotate.eq.Prod] at h_qr
            simp [ProdDropCons_Append_List.eq.MulGet.of.GtLength_0 (show s.length > 0 by grind) n 1] at h_qr ⊢
            have h_r : r = (r' : ℕ) := by simpa [h_q', Nat.mul_zero, Nat.zero_add] using h_q'r'
            simpa [← h_r]
        ·
          simp only [ProdRotate.eq.MulProdS]


-- created on 2026-07-11
