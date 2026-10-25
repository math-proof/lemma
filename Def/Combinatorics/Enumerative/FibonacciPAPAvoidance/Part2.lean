/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push
import Theorem.Combinatorics.Enumerative.FibonacciPAPAvoidance


namespace MetaMathlibExt

def buildPerm (m L : ℕ) (ρ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + L)) where
  toFun i := if h : i.val < m then ⟨(ρ ⟨i.val, h⟩).val, by have := (ρ ⟨i.val, h⟩).isLt; omega⟩
             else ⟨2*m + L - 1 - i.val, by have := i.isLt; omega⟩
  invFun i := if h : i.val < m then
      ⟨(ρ.symm ⟨i.val, h⟩).val, by have := (ρ.symm ⟨i.val, h⟩).isLt; omega⟩
              else ⟨2*m + L - 1 - i.val, by have := i.isLt; omega⟩
  left_inv i := by
    by_cases h : i.val < m
    · have hv : (ρ ⟨i.val, h⟩).val < m := (ρ ⟨i.val, h⟩).isLt
      simp only [h, dite_eq_left, hv]
      apply Fin.ext
      simp only [Fin.eta, Equiv.symm_apply_apply]
    · simp only [h, dite_eq_right, not_false_iff]
      have hib : i.val < m + L := i.isLt
      have : ¬ (2*m + L - 1 - i.val < m) := by omega
      simp only [this, dite_eq_right, not_false_iff]
      apply Fin.ext
      simp only
      omega
  right_inv i := by
    by_cases h : i.val < m
    · have hv : (ρ.symm ⟨i.val, h⟩).val < m := (ρ.symm ⟨i.val, h⟩).isLt
      simp only [h, dite_eq_left, hv]
      apply Fin.ext
      simp only [Fin.eta, Equiv.apply_symm_apply]
    · simp only [h, dite_eq_right, not_false_iff]
      have hib : i.val < m + L := i.isLt
      have : ¬ (2*m + L - 1 - i.val < m) := by omega
      simp only [this, dite_eq_right, not_false_iff]
      apply Fin.ext
      simp only
      omega

end MetaMathlibExt
