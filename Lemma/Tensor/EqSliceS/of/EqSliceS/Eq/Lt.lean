import Lemma.Tensor.GetGetSlice.eq.Get.of.Lt_Min_Length
import Lemma.Algebra.LtVal
import Lemma.Algebra.LengthSlice.eq.Min
import Lemma.Algebra.EqMin.of.Le
import Lemma.Algebra.Le.of.Lt_Add_1
import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Tensor.Eq.is.All_EqGetS
open Tensor Algebra


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
  by_cases h : i.val = n
  ·
    simp only [GetElem.getElem]
    repeat rw [GetGetSlice.eq.Get.of.Lt_Min_Length.fin]
    aesop
  ·
    have h_i := LtVal i
    simp only [LengthSlice.eq.Min] at h_i
    simp only [Tensor.length] at h_i
    rw [EqMin.of.Le (by omega)] at h_i
    have h_i := Le.of.Lt_Add_1 h_i
    have h := Lt.of.Le.Ne h h_i
    simp only [GetElem.getElem]
    repeat rw [GetGetSlice.eq.Get.of.Lt_Min_Length.fin]
    ·
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
    repeat simp only [Tensor.length]; omega


-- created on 2025-08-04
-- updated on 2025-08-05
