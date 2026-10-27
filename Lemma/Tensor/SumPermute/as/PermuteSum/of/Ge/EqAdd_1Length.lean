import Def.Data.Holor.Prod
import Notation.Data.Holor.Permute
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Int.OfNat.eq.Cast
import Lemma.List.Append_TakeDrop.eq.Take.of.Ge
import Lemma.List.EraseIdxPermute__Neg.eq.EraseIdx.of.Ge
import Lemma.List.EraseIdxRotate.eq.AppendEraseIdxDrop.of.GtLength_Add
import Lemma.List.GetRotate.eq.Ite.of.GeLength.GtLength
import Lemma.List.MulLengthSlice_Mul.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.List.Prod.eq.MulProdEraseIdx.of.GtLength
import Lemma.List.ProdDrop.eq.Get.of.EqLength_Add_1
import Lemma.List.ProdDrop.eq.MulProdS
import Lemma.List.ProdRotate.eq.MulProdS
import Lemma.List.ProdRotate.eq.Prod
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.TakeTake.eq.Take
import Lemma.Nat.EqMod_1'0
import Lemma.Nat.ToNatSub_Neg.eq.Add_1
import Lemma.Tensor.DataSelect.as.FlattenGetSliceSplitAtData
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.Sum.eq.Sum_Select
import Lemma.Tensor.SumCast.as.Sum.of.Eq
import Lemma.Vector.GetTranspose.eq.Get
import Def.Data.Holor.Sum
open Nat Vector List Bool Int Tensor Fin Set
set_option maxHeartbeats 250000


private lemma get_tail
  [AddCommMonoid α]
  [NeZero (d : ℕ)]
  {s : List ℕ}
  {i : Fin s.length}
  (h : ↑i + 1 = s.length)
  (h_d : ↑i ≥ d)
  (h_i : ↑i = s.length - 1)
  (X : Tensor α s)
  (t k q r q' r' : ℕ)
  (h_t : t < s[↑i])
  (_ : q < (s.take (↑i - d)).prod)
  (h_r : r < ((s.drop (↑i - d)).take d).prod)
  (h_q_div : q = k / ((s.drop (↑i - d)).take d).prod)
  (h_r_mod : r = k % ((s.drop (↑i - d)).take d).prod)
  (h_q'_div : q' = k / (s.drop (↑i + 1)).prod)
  (h_r'_mod : r' = k % (s.drop (↑i + 1)).prod)
  (h_sub_min_eq : (d + 1) ⊓ s.length - 1 = d)
  (h_sub_eq : s.length - (d + 1) = ↑i - d)
  (h_k : k < (s.eraseIdx ↑i).prod)
  (h_lt :
    (q * s[i] + t) * ((s.drop (↑i - d)).take d).prod + r <
      (s.take (s.length - (d + 1))).prod * ((s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1)).prod) :
  ((X.data.splitAt (s.length - (d + 1))).map fun data =>
      cast (by rw [ProdRotate.eq.MulProdS])
        (data.splitAt (((d + 1) ⊓ s.length - 1) % (s.drop (s.length - (d + 1))).length)).transpose.flatten).flatten.get
    ⟨(q * s[↑i] + t) * ((s.drop (↑i - d)).take d).prod + r, h_lt⟩ =
    X.data.get ⟨(q' * s[↑i] + t) * (s.drop (↑i + 1)).prod + r', by
      have hnil : s.drop (↑i + 1) = [] := Drop.eq.Nil.of.LeLength (show ↑i + 1 ≥ s.length by simp [h_i]; omega)
      simp [hnil] at h_q'_div h_r'_mod ⊢
      rw [EqMod_1'0] at h_r'_mod
      simp [h_q'_div, h_r'_mod]
      rw [Prod.eq.MulProdEraseIdx.of.GtLength (i := ↑i) (by simp)]
      exact AddMul.lt.Mul.of.Lt.Lt h_k h_t⟩ := by
  let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
  have h_rₐ := rₐ.isLt
  simp only [ProdRotate.eq.MulProdS] at h_rₐ
  let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
  simp
  rw [GetCast.eq.Get.of.Eq.fin]
  ·
    let ⟨qₑ, rₑ, h_qₑrₑ⟩ := Any_Eq_AddMul.of.Lt_Mul h_rₐ
    let ⟨h_qₑ_div, h_rₑ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₑrₑ
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₑrₑ]
    rw [GetTranspose.eq.Get.fin]
    repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    apply congrArg
    simp [Drop.eq.Nil.of.LeLength (show i + 1 ≥ s.length by simp [h_i]; omega)] at ⊢ h_q'_div h_r'_mod
    rw [EqMod_1'0] at h_r'_mod
    simp [h_q'_div, h_r'_mod]
    simp [h_sub_eq] at ⊢ h_qₑ_div h_rₑ_mod h_qₐ_div h_rₐ_mod
    have h_q_div := h_q_div
    simp [h_sub_min_eq] at ⊢ h_qₑ_div h_rₑ_mod h_qₐ_div h_rₐ_mod h_r_mod
    simp only [ProdRotate.eq.Prod] at h_qₐ_div h_rₐ_mod
    simp [show s.length - (i - d) = d + 1 by simp [h_i]; omega] at ⊢ h_qₑ_div h_rₑ_mod
    simp [EqAddSub.of.Ge h_d]
    simp [h_qₑ_div, h_rₑ_mod]
    rw [ProdDrop.eq.MulProdS s (i - d) d] at h_qₐ_div h_rₐ_mod
    rw [EqAddSub.of.Ge h_d] at h_qₐ_div h_rₐ_mod
    rw [Div_Mul.eq.DivDiv] at h_qₐ_div
    rw [ProdDrop.eq.Get.of.EqLength_Add_1 h.symm] at *
    rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₐ_div
    simp [Div.eq.Zero.of.Lt h_r] at h_qₐ_div
    rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)] at h_qₐ_div
    simp [MulAdd.eq.AddMulS, MulMul.comm, AddAdd.eq.Add_Add, MulMul.eq.Mul_Mul, h_r_mod] at h_rₐ_mod
    rw [EqMod.of.Lt] at h_rₐ_mod
    ·
      simp [h_qₐ_div, h_rₐ_mod]
      rw [DivAddMul.eq.Add_Div.of.Gt_0 (by grind)]
      simp [Add_Add.eq.AddAdd]
      simp [h_q_div]
      rw [ProdDrop.eq.MulProdS s (i - d) d]
      rw [EqAddSub.of.Ge h_d]
      rw [ProdDrop.eq.Get.of.EqLength_Add_1 h.symm]
      rw [Mul_Mul.eq.MulMul]
      simp [AddMulS.eq.MulAdd]
      left
      erw [Div.eq.Zero.of.Lt h_t]
      apply EqAddMulDiv
    ·
      conv_rhs => rw [Mul.comm]
      apply AddMul.lt.Mul.of.Lt.Lt h_t
      apply LtMod.of.Gt_0
      grind
  ·
    simp [Rotate.eq.AppendDrop__Take]


@[path]
private lemma main
  [AddCommMonoid α]
  [NeZero (d : ℕ)]
  {i : Fin s.length}
-- given
  (h : i.val + 1 = s.length)
  (h_d : i ≥ d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).sum (i - d) ≃ X.sum i := by
-- proof
  simp [@Tensor.Permute.eq.Ite]
  have h_toNat := ToNatSub_Neg.eq.Add_1 d
  have := NeZero.pos d
  split_ifs with h_d0 h_pos? h_i0 h_i
  repeat omega
  rw [SumCast.eq.Cast_Sum.of.Eq]
  ·
    apply SEqCast.of.SEq.Eq
    ·
      rw [h_toNat]
      rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i]
    ·
      rw [h_toNat]
      unfold permuteTail Tensor.rotate
      simp
      rw [Sum.eq.Sum_Select]
      rw [Sum.eq.Sum_Select.of.GtLength (by simp; omega)]
      have h_eraseIdx : (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1)).eraseIdx (↑i - d) = s.eraseIdx ↑i := by
        rw [EraseIdxAppend.eq.Append_EraseIdx.of.LeLength (by simp; omega)]
        simp
        rw [EraseIdxRotate.eq.AppendEraseIdxDrop.of.GtLength_Add (by simp; omega)]
        conv_rhs => rw [EraseIdx.eq.Append_Drop_Add_1]
        rw [EqMin.of.Le (by omega)]
        simp [h_i]
        rw [@Nat.SubSub.eq.Sub_Add (b := 1)]
        rw [Add.comm (a := 1)]
        simp
        rw [AddAdd.eq.Add_Add]
        rw [EqAddSub.of.Ge (by omega)]
        simp
        rw [EqAddSub.of.Ge (by omega)]
        simp
        have := Append_TakeDrop.eq.Take.of.Ge (s := s) (i := s.length - 1) (d := d) (by omega)
        rw [@Nat.SubSub.eq.Sub_Add (b := 1)] at this
        rwa [Add.comm (a := 1)] at this
      have h_get : (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))[↑i - d]'(by simp; omega) = s[i] := by
        rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength (by simp; omega)]
        rw [GetRotate.eq.Ite.of.GeLength.GtLength (by simp; omega) (by simp; omega)]
        simp_all
        split_ifs with h_lt
        ·
          simp [EqMin.of.Le (show (d + 1) ≤ s.length by omega)]
          simp only [GetElem.getElem]
          apply congrArg
          simp
          omega
        ·
          omega
      apply SEqSumS.of.All_SEq.Eq.Eq h_eraseIdx h_get
      ·
        intro t
        have h_t := t.isLt
        simp [h_get] at h_t
        have h_length_slice := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))) (d := ↑i - d) (i := t) (by simp; omega) (by simp)
        simp at h_length_slice
        apply SEq.of.SEqDataS.Eq h_eraseIdx
        ·
          rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
          conv_rhs => rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData]
          simp
          apply SEqCastS.of.SEq.Eq.Eq
          ·
            simp [List.Vector.length]
            have := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength (s := (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))) (d := ↑i - d) (i := t) (by simp; omega) (by simp)
            simp_all
          ·
            simp [List.Vector.length]
            rw [MulLengthSlice_Mul.eq.ProdEraseIdx.of.GtGet.GtLength]
            simp_all
          ·
            apply SEq.of.All_EqGetS.Eq.fin
            ·
              intro k
              have h_k := k.isLt
              let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_k
              have h_q := q.isLt
              have h_r := r.isLt
              let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
              simp [List.Vector.length] at h_q h_k
              have := LengthSlice.eq.ProdTake.of.GtGet.GtLength (s := (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1))) (d := ↑i - d) (i := t) (by simp; omega) (by simp)
              simp at this
              rw [this] at h_q
              rw [h_length_slice, h_eraseIdx] at h_k
              have h_lt : k < (⟨t, (X.data.splitAt (i + 1)).length, s[i.val]⟩ : Slice).length (s.take (i + 1)).prod * (s.drop (↑i + 1)).prod := by
                simpa [MulLengthSlice_Mul.eq.ProdEraseIdx.of.GtGet.GtLength _ h_t]
              let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_lt
              have h_q' := q'.isLt
              simp [List.Vector.length] at h_q'
              let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
              have h_prod := ProdTake.eq.MulProdTake.of.GtLength (show i < s.length by omega)
              have h_prod' := ProdTake.eq.MulProdTake.of.GtLength (show ↑i - d < (s.take (s.length - (d + 1)) ++ (s.drop (s.length - (d + 1))).rotate ((d + 1) ⊓ s.length - 1)).length by simp; omega)
              repeat rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (by assumption)]
              repeat rw [GetGetSlice.eq.Get.of.GtGet.GtLength (by grind) (by omega)]
              repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
              rw [GetCast.eq.Get.of.Eq.fin (by simp)]
              simp [h_get]
              simp [EqMin.of.Le (show (d + 1) ≤ s.length by omega)]
              simp [DropAppend.eq.Drop.of.LeLength (show (↑i - d + 1) ≥ (s.take (s.length - (d + 1))).length by simp; omega)] at ⊢ h_r h_q_div h_r_mod
              simp [show (↑i - d + 1 - (s.length - (d + 1))) = 1 by simp [h_i]; omega] at ⊢ h_r h_q_div h_r_mod
              have h_sub_min_eq : (d + 1) ⊓ s.length - 1 = d := by omega
              simp [h_sub_min_eq] at h_r h_q_div h_r_mod
              simp [TailRotate.eq.Take.of.EqLength_Add_1 (show (s.drop (s.length - (d + 1))).length = d + 1 by simp; omega)] at ⊢ h_r h_q_div h_r_mod
              have h_sub_eq : s.length - (d + 1) = i - d := by
                simp [h_i]
                omega
              simp [h_sub_eq] at ⊢ h_q h_r h_q_div h_r_mod
              rw [TakeAppend.eq.Take.of.GeLength (show (↑i - d) ≤ (s.take (i - d)).length by simp; omega)] at h_q
              rw [TakeTake.eq.Take] at h_q
              exact get_tail h h_d h_i X (↑t) (↑k) (↑q) (↑r) (↑q') (↑r') h_t h_q h_r h_q_div h_r_mod h_q'_div h_r'_mod h_sub_min_eq h_sub_eq h_k (by
                simp [h_sub_eq]
                simp only [ProdRotate.eq.Prod]
                rw [ProdDrop.eq.MulProdS s (i - d) d]
                rw [EqAddSub.of.Ge h_d]
                rw [Mul_Mul.eq.MulMul, MulMul.comm]
                apply AddMul.lt.Mul.of.Lt.Lt _ h_r
                rw [ProdDrop.eq.Get.of.EqLength_Add_1 h.symm]
                apply AddMul.lt.Mul.of.Lt.Lt h_q h_t)
            ·
              simp [List.Vector.length]
              rw [MulLengthSlice_Mul.eq.ProdEraseIdx.of.GtGet.GtLength]
              rw [h_length_slice]
              simp_all
              exact h_t
  ·
    rw [h_toNat]
    rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 h_i]
  ·
    omega


-- created on 2025-11-16
-- updated on 2026-10-26
