import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EqLengthSlice_CoeMul.of.Lt
import Lemma.List.LengthSlice.eq.One.of.Lt
import Lemma.List.MapCast.eq.Cast_Map.of.Eq
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.List.ProdTake.eq.MulProdTake.of.Lt_Length
import Lemma.List.ProdTakeMapCast.eq.CastProdTake
import Lemma.Nat.LtVal
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import Lemma.Tensor.SEqStack_Get.of.GtLength_0
import Lemma.Tensor.SelectCast.eq.Cast_Select.of.Eq
import Lemma.Tensor.Select_0.eq.Cast_Get.of.GtLength_0
import Lemma.Vector.FlattenCast.eq.Cast_Flatten.of.Eq.Eq
import Lemma.Vector.FlattenMapRange.eq.Cast_UFn_0
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.Indices.eq.Cast_MapRange
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import stdlib.SEq
import sympy.tensor.tensor
open Bool List Nat Tensor Vector


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select ⟨d, h⟩ i).data ≃ (X.data.splitAt (d + 1))[i :: s[d]].flatten := by
-- proof
  simp
  induction d generalizing s X with
  | zero =>
    simp
    match s with
    | [] =>
      contradiction
    | s₀ :: s =>
      rw [Select_0.eq.Cast_Get.of.GtLength_0]
      rw [DataCast.eq.Cast_Data.of.Eq (by simp)]
      simp only [List.Vector.length]
      apply SEqCast.of.SEq.Eq.Eq (by simp)
      ·
        simp [LengthSlice.eq.One.of.Lt]
      ·
        have := DataGet.as.GetSplitAtData.of.GtLength_0.fin h X i
        apply SEq.trans this
        unfold List.Vector.getSlice
        simp [List.Vector.length]
        simp [GetElem.getElem]
        rw [GetSplitAt_1.eq.GetUnflatten.fin]
        have h_i := LtVal i
        conv_rhs at h_i => simp
        have := Indices.eq.Cast_MapRange.comm ⟨i, h_i⟩ 1
        simp at this
        rw [this]
        rw [MapCast.eq.Cast_Map.of.Eq]
        ·
          simp
          rw [FlattenCast.eq.Cast_Flatten.of.Eq.Eq]
          ·
            apply SEq_Cast.of.SEq.Eq.Eq
            ·
              simp [LengthSlice.eq.One.of.Lt]
            ·
              simp [LengthSlice.eq.One.of.Lt]
            ·
              rw [FlattenMapRange.eq.Cast_UFn_0]
              apply SEq_Cast.of.SEq.Eq.Eq
              ·
                simp
              ·
                simp
              ·
                rw [GetSplitAt_1.eq.GetUnflatten.fin]
          ·
            simp [LengthSlice.eq.One.of.Lt]
          ·
            rfl
        ·
          simp [LengthSlice.eq.One.of.Lt]
  | succ d ih =>
    have h_X := SEqStack_Get.of.GtLength_0 (by omega) X
    have h_X := EqCast.of.SEq h_X
    conv_lhs => rw [← h_X]
    have h_s := List.EqCons_Tail.of.GtLength_0 (s := s) (by omega)
    have := SelectCast.eq.Cast_Select.of.Eq h_s (([i<s[0]] (X[i]'(Tensor.Lt_Length.of.GtLength_0 (by omega) X i)))) ⟨d + 1, by simp; grind⟩ ⟨i, by grind⟩
    simp at this
    simp [this]
    rw [Tensor.DataCast.eq.Cast_Data.of.Eq (by grind)]
    apply SEqCast.of.SEq.Eq.Eq (by grind)
    .
      sorry
    .
      have h := GtSub.of.Gt_Add h
      apply SEq.of.All_EqGetS.Eq
      ·
        intro t
        have h_t := LtVal t
        sorry
      ·
        simp
        rw [ProdTakeMapCast.eq.CastProdTake]
        rw [ProdTake.eq.MulProdTake.of.Lt_Length (by omega)]
        rw [EqLengthSlice_CoeMul.of.Lt (by omega)]
        rw [ProdEraseIdx.eq.MulProdS]
        simp
        sorry


-- created on 2025-11-10
-- updated on 2025-11-11
