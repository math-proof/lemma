import sympy.sets.fancyset
import sympy.tensor.tensor
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Hyperreal.XEqSumS.of.All_XEq.All_Ge_0
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
import Lemma.List.AddMul_ProdDrop.lt.Prod
import Lemma.List.Get.dvd.ProdTake.of.GtLength
import Lemma.List.LengthSlice.eq.ProdTake.of.GtGet.GtLength
import Lemma.List.ProdTake.eq.DivProdTake.of.Ne_0.GtLength
import Lemma.Nat.LtAddMul.of.Lt.Lt_Div.Dvd
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.DataSum.eq.Sum_DataSelect
import Lemma.Tensor.Sum.as.Sum.of.LeLength
import Lemma.Tensor.XEq.is.All_XEqGetS
import Lemma.Tensor.XEq.is.XEqDataS
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetSum.eq.Sum_Get
import Lemma.Vector.GetGetSlice.eq.Get.of.GtGet.GtLength
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.XEq.is.All_XEqGetS
open Hyperreal Tensor Fin Vector List Nat

set_option maxHeartbeats 8000000


private lemma data_ge_of_ge
  {A : Tensor ℝ* s}
  (h_pos : A ≥ 0) :
  ∀ k : Fin s.prod, (0 : ℝ*) ≤ A.data[k] := by
  intro k
  have h' := h_pos k
  simp only [LE.le] at h'
  rw [show ((0 : Tensor ℝ* s).data)[k] = 0 from EqGet0_0.fin (α := ℝ*) k] at h'
  exact ge_iff_le.mp h'


private lemma select_flat_idx_lt
  {s : List ℕ} {i : ℕ}
  (hi : i < s.length)
  (k : Fin s[i])
  {q : Fin ((⟨↑↑k, ↑(s.take (i + 1)).prod, ↑s[i]⟩ : Slice).length (s.take (i + 1)).prod)}
  {r : Fin (s.drop (i + 1)).prod} :
  (q * s[i] + k) * (s.drop (i + 1)).prod + r < s.prod := by
  have h_length_slice := LengthSlice.eq.ProdTake.of.GtGet.GtLength.simp hi k.isLt
  have h_q := q.isLt
  have h_i : q < (s.take i).prod := by rwa [← h_length_slice]
  have h_div := DivProdTake.eq.ProdTake.of.Ne_0.GtLength hi (by grind)
  have h_dvd := Get.dvd.ProdTake.of.GtLength hi
  have h_idx : q * s[i] + k < (s.take (i + 1)).prod :=
    LtAddMul.of.Lt.Lt_Div.Dvd h_dvd (by rwa [h_div]) k.isLt
  simpa using AddMul_ProdDrop.lt.Prod (d := i + 1) ⟨q * s[i] + k, h_idx⟩ r


private lemma select_data_get
  {s : List ℕ} {i : ℕ}
  (hi : i < s.length)
  (A : Tensor ℝ* s)
  (k : Fin s[i])
  (j : Fin (s.eraseIdx i).prod)
  {q : Fin ((⟨↑↑k, ↑(s.take (i + 1)).prod, ↑s[i]⟩ : Slice).length (s.take (i + 1)).prod)}
  {r : Fin (s.drop (i + 1)).prod}
  (hqr : ↑j = ↑q * (s.drop (i + 1)).prod + ↑r) :
  (A.select ⟨i, hi⟩ k).data.get j =
    A.data.get ⟨(q * s[i] + k) * (s.drop (i + 1)).prod + r, select_flat_idx_lt hi k⟩ := by
  simp only [Tensor.select, GetElem.getElem]
  have hlen := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp hi k.isLt
  rw [GetCast.eq.Get.of.Eq.fin hlen]
  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin hqr]
  erw [GetGetSlice.eq.Get.of.GtGet.GtLength hi k.isLt]
  rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  simp


@[main]
private lemma main
  {A B : Tensor ℝ* s}
-- given
  (h_pos : B ≥ 0)
  (h_xeq : A ≈ B)
  (i : ℕ) :
-- imply
  A.sum i ≈ B.sum i := by
-- proof
  if h : s.length ≤ i then
    have hs := EqEraseIdx.of.LeLength h
    rw [Tensor.XEq.is.XEqDataS, Sum.eq.Cast_Sum.of.LeLength h]
    conv_rhs => rw [Sum.eq.Cast_Sum.of.LeLength h]
    rw [DataCast.eq.Cast_Data.of.Eq hs.symm A, DataCast.eq.Cast_Data.of.Eq hs.symm B]
    apply Vector.XEq.of.All_XEqGetS.fin
    intro t
    rw [GetCast.eq.Get.of.Eq.fin (by grind)]
    rw [GetCast.eq.Get.of.Eq.fin (by grind)]
    apply Vector.All_XEqGetS.of.XEq.fin (XEqDataS.of.XEq h_xeq) ⟨t, by grind⟩
  else
    have hi : i < s.length := Nat.lt_of_not_ge h
    have h_ge := data_ge_of_ge h_pos
    have h_xeq_data := XEqDataS.of.XEq h_xeq
    rw [Tensor.XEq.is.XEqDataS]
    rw [DataSum.eq.Sum_DataSelect A ⟨i, hi⟩, DataSum.eq.Sum_DataSelect B ⟨i, hi⟩]
    refine Vector.XEq.of.All_XEqGetS.fin ?_
    intro j
    conv_lhs => rw [GetSum.eq.Sum_Get.fin (s := Finset.univ) (x := fun k => (A.select ⟨i, hi⟩ k).data) j]
    conv_rhs => rw [GetSum.eq.Sum_Get.fin (s := Finset.univ) (x := fun k => (B.select ⟨i, hi⟩ k).data) j]
    apply Hyperreal.XEqSumS.of.All_XEq.All_Ge_0
    ·
      intro k
      have hlen := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp hi k.isLt
      have hj := Nat.lt_of_lt_of_eq j.isLt hlen.symm
      obtain ⟨q, r, hqr⟩ := Any_Eq_AddMul.of.Lt_Mul hj
      refine ge_iff_le.mpr ?_
      rw [select_data_get hi B k j hqr]
      exact h_ge ⟨(q * s[i] + k) * (s.drop (i + 1)).prod + r, select_flat_idx_lt hi k⟩
    ·
      intro k
      have hlen := MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp hi k.isLt
      have hj := Nat.lt_of_lt_of_eq j.isLt hlen.symm
      obtain ⟨q, r, hqr⟩ := Any_Eq_AddMul.of.Lt_Mul hj
      have hA := select_data_get hi A k j hqr
      have hB := select_data_get hi B k j hqr
      calc
        _ = A.data.get ⟨(q * s[i] + k) * (s.drop (i + 1)).prod + r, select_flat_idx_lt hi k⟩ := hA
        _ ≈ B.data.get ⟨(q * s[i] + k) * (s.drop (i + 1)).prod + r, select_flat_idx_lt hi k⟩ := All_XEqGetS.of.XEq h_xeq_data ⟨(q * s[i] + k) * (s.drop (i + 1)).prod + r, select_flat_idx_lt hi k⟩
        _ = (B.select ⟨i, hi⟩ k).data.get j := hB.symm


-- created on 2026-07-26
