import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.LengthSlice.eq.One.of.Lt
import Lemma.Nat.LtVal
import Lemma.Tensor.DataCast.eq.Cast_Data.of.Eq
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import Lemma.Tensor.Select_0.eq.Cast_Get.of.GtLength_0
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten
import Lemma.Vector.Indices.eq.Cast_MapRange
import stdlib.SEq
import sympy.tensor.tensor
open Bool List Tensor Vector Nat


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
        simp
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
        sorry
  | succ d ih =>
    sorry


-- created on 2025-11-10
