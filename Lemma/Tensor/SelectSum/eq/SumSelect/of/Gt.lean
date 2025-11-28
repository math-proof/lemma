import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.Nat.ValCast.eq.Val.of.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Finset.Sum.of.All_Eq.Eq
import Lemma.List.DropEraseIdx.eq.AppendDropTake.of.Ge
import Lemma.List.EraseIdxEraseIdx.of.Gt.GtLength
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.GtLength
import Lemma.List.LengthSlice.eq.ProdTake.of.Lt_Get.GtLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength
import Lemma.List.Prod.eq.MulProdS
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.List.ProdTake.eq.MulProdTake.of.GtLength
import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.NotGe.is.Lt
import Lemma.Tensor.DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0
import Lemma.Tensor.DataSum.eq.Sum_DataSelect
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqSelectS.of.SEq
import Lemma.Tensor.SEqSum.of.LeLength
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.Sum_Get
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.Sum.of.All_Eq.Eq
open Bool Finset List Nat Tensor Vector
set_option maxHeartbeats 4000000


@[main, comm]
private lemma main
  [AddCommMonoid α]
  {d : Fin s.length}
  {k : ℕ}
-- given
  (h_d : k > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.sum k).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ (X.select d i).sum (k - 1) := by
-- proof
  if h_k : k ≥ s.length then
    have := SEqSum.of.LeLength (show (s.eraseIdx ↑d).length ≤ k - 1 by grind) (X.select d i)
    apply SEq.symm ∘ SEq.trans this
    apply SEqSelectS.of.SEq
    apply SEq_Sum.of.LeLength h_k
  else
    have h_k := Lt.of.NotGe h_k
    apply SEq.of.SEqDataS.Eq
    ·
      rwa [← EraseIdxEraseIdx.of.Gt.GtLength (by omega)]
    ·
      rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0.simp]
      apply SEqCast.of.SEq.Eq
      ·
        simp
        rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
        grind
      ·
        rw [DataSum.eq.Sum_DataSelect (X.select d i) ⟨k - 1, by grind⟩]
        apply SEq.of.All_EqGetS.Eq.fin
        ·
          intro t
          have h_t := t.isLt
          simp
          let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_t
          let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
          have h_q := q.isLt
          simp at h_q
          have h_i : ↑i < (s.eraseIdx k)[d.val]'(by grind) := by
            rw [GetEraseIdx.eq.Get.of.Gt.GtLength h_k h_d]
            grind
          rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (by grind) h_i] at h_q
          have h_r := r.isLt
          rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
          rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin.fin _ _ h_i]
          ·
            rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
            rw [GetSum.eq.Sum_Get.fin]
            simp [GetEraseIdx.eq.Get.of.Gt.GtLength h_k h_d]
            simp [DropEraseIdx.eq.AppendDropTake.of.Ge h_d]
            rw [DataSum.eq.Sum_DataSelect X ⟨k, by grind⟩]
            rw [GetSum.eq.Sum_Get.fin]
            have h_cast := (GetEraseIdx.eq.Get.of.Lt.GtLength h_k h_d).symm
            apply @Finset.Sum.of.All_Eq.Eq (h_n := h_cast)
            intro j
            have h_j := j.isLt
            rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0.simp]
            rw [GetCast.eq.Get.of.Eq.fin]
            ·
              simp
              rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0.simp]
              rw [GetCast.eq.Get.of.Eq.fin]
              ·
                simp
                simp at h_t
                rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (by grind) (by omega)] at h_t
                have h_lt : t < (⟨↑↑(cast (congrArg Fin h_cast) j), ↑((s.eraseIdx ↑d).take (k - 1 + 1)).prod, (s.eraseIdx d)[k - 1]'(by grind)⟩ : Slice).length ((s.eraseIdx ↑d).take (k - 1 + 1)).prod * ((s.eraseIdx ↑d).drop (k - 1 + 1)).prod := by
                  simp
                  rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
                  rwa [← EraseIdxEraseIdx.of.Gt.GtLength (by omega) (by omega)]
                  grind
                let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
                let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
                have h_lt : (↑q * s[↑d] + ↑i) * (((s.take k).drop (↑d + 1)).prod * (s.drop (k + 1)).prod) + ↑r < (⟨↑↑j, ↑(s.take (k + 1)).prod, ↑s[k]⟩ : Slice).length (s.take (k + 1)).prod * (s.drop (k + 1)).prod := by
                  simp
                  rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength _ h_j]
                  rw [ProdEraseIdx.eq.MulProdS]
                  rw [Prod.eq.MulProdS (s.take k) (d + 1)]
                  rw [TakeTake.eq.Take.of.Ge (by omega)]
                  rw [MulMul.eq.Mul_Mul]
                  apply AddMul.lt.Mul.of.Lt.Lt
                  ·
                    simp
                    apply AddMul.lt.Mul.of.Lt.Lt
                    ·
                      rwa [TakeEraseIdx.eq.Take.of.Ge (show k ≥ d by omega)] at h_q
                    ·
                      grind
                  ·
                    simp [DropEraseIdx.eq.AppendDropTake.of.Ge h_d] at h_r
                    exact h_r
                let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul.fin h_lt
                have h_qₐ := qₐ.isLt
                simp at h_qₐ
                rw [LengthSlice.eq.ProdTake.of.Lt_Get.GtLength (by grind) (by grind)] at h_qₐ
                let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
                rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := qₐ) (j := rₐ)]
                ·
                  rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin.fin _ _ h_j]
                  ·
                    rw [DataSelect.eq.Cast_FlattenGetSliceSplitAtData.of.GtLength_0.simp]
                    rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd.fin.fin _ _ ]
                    .
                      repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
                      rw [GetCast.eq.Get.of.Eq.fin]
                      .
                        simp [h_cast.symm]
                        simp [Nat.ValCast.eq.Val.of.Eq h_cast]
                        simp [EqAddSub.of.Ge (show k ≥ 1 by omega)]
                        simp [List.DropEraseIdx.eq.Drop.of.Le (show d ≤ k by omega)]
                        sorry
                      .
                        -- simp [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
                        sorry
                    .
                      sorry
                    .
                      sorry
                    .
                      sorry
                  ·
                    simp [ProdTake.eq.MulProdTake.of.GtLength h_k]
                  ·
                    simp [ProdTake.eq.MulProdTake.of.GtLength h_k]
                    rwa [EqDivMul.of.Ne_0 (by grind)]
                ·
                  exact h_qₐrₐ
              ·
                simp
                rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
                grind
            ·
              simp
              rwa [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength]
          ·
            simp [ProdTake.eq.MulProdTake.of.GtLength (show (s.eraseIdx k).length > ↑d by grind)]
          ·
            simp [ProdTake.eq.MulProdTake.of.GtLength (show (s.eraseIdx k).length > ↑d by grind)]
            rwa [EqDivMul.of.Ne_0 (by grind)]
        ·
          simp
          rw [MulLengthSlice.eq.ProdEraseIdx.of.Lt_Get.GtLength (by grind)]
          rwa [← EraseIdxEraseIdx.of.Gt.GtLength (by omega)]
          grind


-- created on 2025-11-28
