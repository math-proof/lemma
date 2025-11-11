import Lemma.Tensor.EqLengthStack
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.List.EqLengthSlice
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqGetStack.of.Eq
import Lemma.Vector.EqMapS.of.All_Eq
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.GetMkFlatten.eq.MkGet
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetValIndices.eq.Add.of.Lt
open Tensor List Vector Nat


@[main]
private lemma main
-- given
  (f : ℕ → Tensor α s) :
-- imply
  ([i < n + j] f i)[j :] ≃ [i < n] f (i + j) := by
-- proof
  have h_length := EqLengthStack f (n + j)
  apply SEq.of.All_SEqGetS.Eq.Eq <;>
    simp [h_length]
  ·
    intro i
    have h_i : n = ((⟨j, (Stack (n + j) fun i ↦ f i).length, 1⟩ : Slice).length (Stack (n + j) fun i ↦ f i).length) := by
      simp [h_length]
      rw [AddCoeS.eq.CoeAdd]
      simp [EqLengthSlice]
    have h_ij := EqGetStack.of.Eq h_i (fun i => f (i + j)) i
    simp [GetElem.getElem] at h_ij
    simp [GetElem.getElem]
    simp [h_ij]
    simp [Tensor.getSlice]
    constructor
    ·
      rfl
    ·
      congr
      have h_length_stack : ([i < n + j] f i).length = n + j := by
        simp [EqLengthStack]
      have h_all : ∀ i : Fin ([i < n + j] f i).length, ([i < n + j] f i)[i] = f i := by
        apply EqGetStack.of.Eq
        simp [EqLengthStack]
      have h_map := EqMapS.of.All_Eq h_all (List.Vector.indices ⟨j, ([i < n + j] f i).length, 1⟩ ([i < n + j] f i).length)
      simp [Tensor.get]
      simp [Tensor.length]
      simp [GetElem.getElem]
      rw [GetToVector.eq.Get.cons.fin]
      rw [GetMkFlatten.eq.MkGet]
      apply Eq.of.EqDataS
      simp [GetElem.getElem]
      simp [List.Vector.get]
      congr
      rw [EqGetStack.fin]
      congr
      rw [GetValIndices.eq.Add.of.Lt]
  ·
    rw [AddCoeS.eq.CoeAdd]
    apply EqLengthSlice


-- created on 2024-12-22
-- updated on 2025-06-26
