import Lemma.Tensor.GetGetSlice.eq.Get.of.Lt_Min
import Lemma.List.LengthSlice.eq.Min
import Lemma.Nat.Le.of.Lt_Add_1
import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Nat.Lt_Min.is.Lt.Lt
import Lemma.Tensor.Eq.is.All_EqGetS
open Tensor List Nat
set_option maxHeartbeats 500000


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
  let k : ℕ := n + 1
  change X[:k] = Y[:k]
  apply Eq.of.All_EqGetS
  intro i
  have h_i := i.isLt
  simp [LengthSlice.eq.Min] at h_i
  simp [Tensor.length] at h_i
  have h_min := Lt_Min.of.Lt.Lt h_i.left h_i.right
  simp only [GetElem.getElem]
  have hx := GetGetSlice.eq.Get.of.Lt_Min.fin (n := k) X h_min
  simp at hx
  simp [hx]
  have hy := GetGetSlice.eq.Get.of.Lt_Min.fin (n := k) Y h_min
  simp at hy
  erw [hy]
  if h : ↑i = n then
    simp only [GetElem.getElem] at h₁
    simp [h]
    exact h₁
  else
    have h_i_succ : ↑i < n + 1 := by
      simpa [k] using h_i.left
    have h_le := Le.of.Lt_Add_1 (y := n) h_i_succ
    have h_lt := Lt.of.Le.Ne h_le h
    have h_min_n := Lt_Min.of.Lt.Lt h_lt h_i.right
    have h₀ := All_EqGetS.of.Eq h₀
    have h_i_n : ↑i < (⟨0, n, 1⟩ : Slice).length X.length := by
      simp [LengthSlice.eq.Min, Tensor.length]
      exact ⟨h_lt, h_i.right⟩
    specialize h₀ ⟨↑i, h_i_n⟩
    simp only [GetElem.getElem] at h₀
    have hx0 := GetGetSlice.eq.Get.of.Lt_Min.fin (n := n) X h_min_n
    simp at hx0
    have hy0 := GetGetSlice.eq.Get.of.Lt_Min.fin (n := n) Y h_min_n
    simp at hy0
    rw [← hx0, ← hy0]
    exact h₀


-- created on 2019-03-24
-- updated on 2026-08-27
