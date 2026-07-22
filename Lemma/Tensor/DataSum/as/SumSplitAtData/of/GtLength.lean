import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Fin.Eq_Fin.of.EqVal
import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.ProdEraseIdx.eq.MulProdS
import Lemma.Nat.Div.eq.AddMulDiv_Mul
import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.DataFromVector.eq.FlattenMapData
import Lemma.Tensor.DataGet.as.GetSplitAtData.of.GtLength_0
import Lemma.Tensor.DataSum_0.eq.SumSplitAtData
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.Sum.eq.FromVectorMap_FunSum.of.GtLength
import Lemma.Vector.EqGetS.of.SEq.Lt
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Fin List Nat Tensor Vector


@[main, comm]
private lemma main
  [Add α] [Zero α]
-- given
  (h : i < s.length)
  (X : Tensor α s) :
-- imply
  (X.sum i).data ≃ ((X.data.splitAt i).map fun x => (x.splitAt 1).sum).flatten := by
-- proof
  induction i generalizing s X with
  | zero =>
    cases s with
    | nil =>
      simp at h
    | cons s₀ s =>
      simp [DataSum_0.eq.SumSplitAtData]
      apply SEq.of.All_EqGetS.Eq.fin (by simp)
      intro t
      have h_t := t.isLt
      rw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by grind⟩) (j := ⟨t, by grind⟩) (by grind)]
      simp
      congr 1
      congr 1
      congr 1
      simp
      rw [Head.eq.Get_0.fin]
      ext j
      erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
      simp
  | succ d ih =>
    cases s with
    | nil =>
      simp at h
    | cons s₀ s =>
      have h_lt : d < s.length := Nat.lt_of_succ_le (Nat.lt_succ_iff.mp h)
      unfold Tensor.sum
      simp only [h]
      rw [(Sum.eq.FromVectorMap_FunSum.of.GtLength (s := s) (n := s₀) (by simpa using h_lt) X).symm]
      split_ifs
      ·
        refine SEq.trans (DataCast.as.Data.of.Eq (by grind) (X.sum (d + 1))) ?_
        rw [congrArg Tensor.data (Sum.eq.FromVectorMap_FunSum.of.GtLength (s := s) (n := s₀) (by simpa using h_lt) X)]
        rw [DataFromVector.eq.FlattenMapData]
        apply SEq.of.All_EqGetS.Eq.fin (by simp [ProdEraseIdx.eq.MulProdS]; grind)
        intro t
        have h_t := t.isLt
        simp only [ProdEraseIdx.eq.MulProdS] at h_t
        rw [Drop_Add.eq.DropDrop] at h_t
        let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
        rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
        have h_t : t < ((s₀ :: s).headD 1) * ((s₀ :: s).tail.eraseIdx d).prod := by
          grind
        let ⟨q', r', h_q'r'⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
        let ⟨h_q'_div, h_r'_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_q'r'
        erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_q'r']
        simp
        erw [GetToVector.eq.Get.cons.fin]
        have ih := ih (s := s) (X := X.get q') h_lt
        have ih := EqGetS.of.SEq.Lt.fin (by grind) ih (i := r')
        simp at ih
        apply ih.trans
        have h_r' : r' < (s.take d).prod * ((s.drop d).drop 1).prod := by
          grind
        let ⟨qₐ, rₐ, h_qₐrₐ⟩ := Any_Eq_AddMul.of.Lt_Mul h_r'
        let ⟨h_qₐ_div, h_rₐ_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qₐrₐ
        erw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qₐrₐ]
        simp
        rw [GetSum.eq.SumMapGet.fin]
        erw [GetSum.eq.SumMapGet.fin]
        congr 1
        simp [h_r'_mod] at h_rₐ_mod
        simp [ProdEraseIdx.eq.MulProdS] at h_rₐ_mod
        simp at h_r_mod
        have h_rₐ := h_rₐ_mod.trans h_r_mod.symm
        have h_rₐ := Eq_Fin.of.EqVal h_rₐ
        simp [h_rₐ]
        congr 1
        congr 1
        erw [DataGet.eq.Cast_GetSplitAtData.of.GtLength_0.fin (by grind)]
        ext j
        rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
        simp
        congr 1
        simp
        rw [Add_Add.eq.AddAdd]
        congr 1
        rw [List.Prod.eq.MulProdS s d]
        rw [Mul_Mul.eq.MulMul]
        rw [AddMulS.eq.MulAdd]
        congr 1
        simp only [h_q'_div, h_qₐ_div, h_q_div, h_r'_mod]
        simp [ProdEraseIdx.eq.MulProdS]
        apply AddMulDiv_Mul.eq.Div
      ·
        grind


-- created on 2026-07-22
