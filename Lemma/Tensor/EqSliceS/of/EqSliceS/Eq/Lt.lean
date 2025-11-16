import Lemma.Tensor.GetGetSlice.eq.Get
import Lemma.List.LengthSlice.eq.Min
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.Le.of.Lt_Add_1
import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Tensor.Eq.is.All_EqGetS
open Tensor List Nat


/--
slicing operator is defined as follows:
lean/Init/Data/Array/Subarray.lean
-/
@[main]
private lemma main
  {X Y : Tensor α (s₀ :: s)}
-- given
  (h_n : n < s₀)
  (h₀ : X[:n] = Y[:n])
  (h₁ : X[n] = Y[n]) :
-- imply
  X[:(n + 1 : ℕ)] = Y[:(n + 1 : ℕ)] := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  if h : i.val = n then
    simp only [GetElem.getElem]
    repeat rw [GetGetSlice.eq.Get.fin]
    aesop
  else
    have h_i := i.isLt
    simp only [LengthSlice.eq.Min] at h_i
    simp only [Tensor.length] at h_i
    rw [EqMin.of.Le (by omega)] at h_i
    have h_i := Le.of.Lt_Add_1 h_i
    have h := Lt.of.Le.Ne h_i h
    simp only [GetElem.getElem]
    repeat rw [GetGetSlice.eq.Get.fin]
    have h₀ := All_EqGetS.of.Eq h₀
    simp only [GetElem.getElem] at h₀
    have h_i : i < (⟨0, n, 1⟩ : Slice).length X.length := by
      simp_all [LengthSlice.eq.Min]
      simp [Tensor.length]
      linarith
    specialize h₀ ⟨i, h_i⟩
    repeat rw [GetGetSlice.eq.Get.of.Lt_Min.fin] at h₀
    assumption
    repeat simp_all; linarith


-- created on 2025-08-04
-- updated on 2025-08-05
