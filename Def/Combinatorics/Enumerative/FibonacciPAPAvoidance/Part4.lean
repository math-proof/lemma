/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push
import Theorem.Combinatorics.Enumerative.FibonacciPAPAvoidance.Part3


namespace MetaMathlibExt

def frontFixed {N : ℕ} (b : Fin (N + 1)) (π : Equiv.Perm (Fin (N + 1)))
    (h : IsGood (N + 1) π)
    (hπ : π (Fin.last N) = b) : Equiv.Perm (Fin b.val) where
  toFun i := ⟨(π ⟨i.val, by have := i.isLt; have := b.isLt; omega⟩).val, by
    have hbv : (π (Fin.last N)).val = b.val := by rw [hπ]
    have hlt := front_val π h ⟨i.val, by have := i.isLt; have := b.isLt; omega⟩
      (by rw [hbv]; exact i.isLt)
    rw [hbv] at hlt; exact hlt⟩
  invFun i := ⟨(π.symm ⟨i.val, by have := i.isLt; have := b.isLt; omega⟩).val, by
    have hbv : (π (Fin.last N)).val = b.val := by rw [hπ]
    have hlt := front_symm π h ⟨i.val, by have := i.isLt; have := b.isLt; omega⟩
      (by rw [hbv]; exact i.isLt)
    rw [hbv] at hlt; exact hlt⟩
  left_inv i := by apply Fin.ext; simp only [Fin.eta, Equiv.symm_apply_apply]
  right_inv i := by apply Fin.ext; simp only [Fin.eta, Equiv.apply_symm_apply]

end MetaMathlibExt
