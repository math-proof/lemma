import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.List.LengthSlice.eq.One.of.Lt
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.Prod.eq.MulProdS
import Lemma.Nat.Div.eq.Zero.of.Lt
import Lemma.Nat.Eq_Div.Eq_Mod.of.Eq_AddMul
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtLength
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open Bool Fin List Nat Tensor Vector


@[main, comm, cast]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  X.select ⟨0, h_s⟩ ⟨i, by aesop⟩ ≃ X.get ⟨i, by simpa [Length.eq.Get_0.of.GtLength_0 h_s]⟩ := by
-- proof
  unfold Tensor.select
  apply SEq.of.SEqDataS.Eq (by simp)
  simp
  apply SEqCast.of.SEq.Eq
  ·
    exact MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp (d := 0) h_s h_i
  ·
    apply SEq.of.All_EqGetS.Eq.fin (by
      rw [MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp (d := 0) h_s h_i]
      simp)
    intro t
    have h_cons : ∃ n s', s = n :: s' := by
      match s with
      | [] =>
        exfalso
        simp at h_s
      | n :: s' =>
        exact ⟨n, s', rfl⟩
    obtain ⟨n, s', hs⟩ := h_cons
    subst hs
    let s := n :: s'
    have h_t := t.isLt
    let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
    let ⟨h_q_div, h_r_mod⟩ := Eq_Div.Eq_Mod.of.Eq_AddMul h_qr
    rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
    rw [GetGetSlice.eq.Get.of.GtGet.GtLength h_s h_i]
    have h_prod := ProdTake_1.eq.Get_0.of.GtLength_0 h_s
    have h_slice_nat : (⟨↑i, (s.take 1).prod, s[0]⟩ : Slice).length (s.take 1).prod = 1 := by
      rw [h_prod]
      exact LengthSlice.eq.One.of.Lt (n := s[0]) h_i
    have h_t_lt : ↑t < (s.drop 1).prod := by
      calc ↑t
        _ < (⟨↑i, (s.take 1).prod, s[0]⟩ : Slice).length (s.take 1).prod * (s.drop 1).prod := h_t
        _ = (s.drop 1).prod := by rw [h_slice_nat, one_mul]
    have h_qval : (q : ℕ) = 0 := by
      calc (q : ℕ)
        _ = ↑t / (s.drop 1).prod := h_q_div
        _ = 0 := Div.eq.Zero.of.Lt h_t_lt
    have h_idx : q.val * s[0] + i = i := by simp [h_qval]
    have h_get_idx :
        (X.data.splitAt 1).get ⟨q.val * s[0] + i, by grind⟩ =
          (X.data.splitAt 1).get ⟨i, by grind⟩ := by
      congr 1
      exact Fin.eq_of_val_eq h_idx
    rw [h_get_idx]
    simp only [GetElem.getElem]
    rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
    erw [DataGet.eq.GetUnflattenData.fin]
    erw [GetUnflatten.eq.Get_AddMul.fin]
    congr 1
    apply Fin.eq_of_val_eq
    simp [h_qval, h_qr]


-- created on 2025-10-05
-- updated on 2026-07-23
