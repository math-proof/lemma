import Lemma.Tensor.Slice.of.Eq
import Lemma.Tensor.Get.of.Eq.Lt
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetGetSlice.eq.Get.of.Lt_Min
import Lemma.List.LengthSlice.eq.Min
import Lemma.Nat.Lt_Min.is.Lt.Lt
open Tensor List Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Eq.is.GetSlice.Get |
| comm | Tensor.GetSlice.Get.is.Eq |
| mp | Tensor.GetSlice.Get.of.Eq |
| mpr | Tensor.Eq.of.GetSlice.Get |
-/
@[main, comm, mp, mpr]
private lemma main
  {n : ℕ}
  {X Y : Tensor α ((n + 1) :: s)} :
-- imply
  X = Y ↔ X[:n] = Y[:n] ∧ X[n]'(by simp [Tensor.length]) = Y[n]'(by simp [Tensor.length]) := by
-- proof
  constructor
  ·
    intro h
    constructor
    ·
      apply Slice.of.Eq h
    ·
      exact Get.of.Eq.Lt (by simp) h
  ·
    intro ⟨h_slice, h_n⟩
    apply Eq.of.All_EqGetS
    intro i
    have hi : (i : ℕ) < n + 1 := by
      simpa [Tensor.length] using i.isLt
    by_cases hlt : (i : ℕ) < n
    ·
      have h_bound := Lt_Min.of.Lt.Lt hlt hi
      have hi_slice : (i : ℕ) < X[:n].length := by
        simp [LengthSlice.eq.Min, Tensor.length]
        exact hlt
      have hx := GetGetSlice.eq.Get.of.Lt_Min X h_bound
      have hy := GetGetSlice.eq.Get.of.Lt_Min Y h_bound
      have h_gets := All_EqGetS.of.Eq h_slice ⟨i, hi_slice⟩
      simp only [GetElem.getElem] at hx hy h_gets ⊢
      apply Eq.trans hx.symm
      apply Eq.trans _ hy
      convert h_gets
      exact Iff.rfl
    ·
      have hineq : (i : ℕ) = n := Nat.eq_of_lt_succ_of_not_lt hi hlt
      simp only [GetElem.getElem] at h_n ⊢
      convert h_n
      · apply Fin.eq_of_val_eq; exact hineq
      · apply Fin.eq_of_val_eq; exact hineq


-- created on 2023-03-22
-- updated on 2026-09-19
