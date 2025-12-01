import Lemma.Vector.SEq.of.EqLength_0.EqLength_0
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Tensor.All_SEqDataSGet.of.All_SEqGetS.Eq
import Lemma.Bool.IffEqS.of.Eq
import Lemma.Nat.Ge.of.NotLt
import Lemma.List.GetElem.eq.None.of.LeLength
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Tensor.Data.eq.FlattenMapRange
import Lemma.Vector.GetVal.eq.Get.of.Lt
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Vector.EqGetRange
import Lemma.List.EqGetS.of.Eq.GtLength
import Lemma.Tensor.HEq.of.SEqDataS.Eq
import Lemma.Nat.Eq.of.EqValS
import Lemma.Vector.EqValS.of.SEq
import Lemma.Vector.SEq.of.EqValS
open Tensor Vector List Bool Nat Fin


@[main]
private lemma main
  {A : Tensor α (n :: s₀)}
  {B : Tensor α (m :: s₁)}
-- given
  (h₀ : n = m)
  (h₁ : s₀ = s₁)
  (h₂ : ∀ i : Fin n, A[i] ≃ B[(⟨i, by simp [← h₀]⟩ : Fin m)]) :
-- imply
  A ≃ B := by
-- proof
  if h_n : n = 0 then
    constructor
    ·
      rw [h_n]
      rw [h_n] at h₀
      rw [← h₀]
      simp
      assumption
    ·
      apply HEq.of.SEqDataS.Eq (by simp_all)
      apply SEq.of.EqLength_0.EqLength_0 <;>
      ·
        simp [List.Vector.length]
        simp_all
  else
    constructor
    ·
      rw [h₀]
      simp
      assumption
    ·
      have h₂ := All_SEqDataSGet.of.All_SEqGetS.Eq h₀ h₂
      have h_n := Gt_0.of.Ne_0 h_n
      apply HEq.of.SEqDataS.Eq (by simp_all)
      apply SEq.of.EqValS
      ext k x
      if h : k < A.data.val.length then
        simp_all
        apply IffEqS.of.Eq
        repeat rw [GetVal.eq.Get.of.Lt (by simp_all)]
        rw [← h₀, ← h₁] at h
        let ⟨q, r, h_eq⟩ := Any_Eq_AddMul.of.Lt_Mul h
        simp [Data.eq.FlattenMapRange, h_eq]
        let v_n : List.Vector (List.Vector α s₀.prod) n := (List.Vector.range n).map fun i ↦ A[i].data
        have h_a := GetFlatten_AddMul.eq.Get v_n
        simp at h_a
        have h_r : r.val < s₁.prod := by
          rw [← h₁]
          simp
        have h_q : q < m := by
          rw [← h₀]
          simp
        let v_m : List.Vector (List.Vector α s₁.prod) m := (List.Vector.range m).map fun i ↦ B[i].data
        have h_b := GetFlatten_AddMul.eq.Get v_m ⟨q, h_q⟩ ⟨r, h_r⟩
        simp [← h₁] at h_b
        simp [v_n] at h_a
        rw [h_a]
        simp [v_m] at h_b
        rw [h_b]
        simp [GetElem.getElem]
        repeat rw [EqGetRange.fin]
        simp [List.Vector.get]
        repeat rw [GetVal.eq.Get.of.Lt (by simp_all)]
        have hq := h₂ q
        have hq := EqValS.of.SEq hq
        apply EqGetS.of.Eq.GtLength (show r < A[q].data.val.length by simp_all) hq
      else
        apply IffEqS.of.Eq
        have h := Ge.of.NotLt h
        rw [GetElem.eq.None.of.LeLength h]
        simp_all


-- created on 2025-05-23
-- updated on 2025-07-20
