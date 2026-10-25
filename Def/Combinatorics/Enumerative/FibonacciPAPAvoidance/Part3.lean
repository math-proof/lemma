/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push
import Theorem.Combinatorics.Enumerative.FibonacciPAPAvoidance.Part2


namespace MetaMathlibExt

def frontPerm {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
    Equiv.Perm (Fin (π (Fin.last N)).val) where
  toFun i := ⟨(π ⟨i.val, by have := i.isLt; have := (π (Fin.last N)).isLt; omega⟩).val,
              front_val π h ⟨i.val, by have := i.isLt; have := (π (Fin.last N)).isLt; omega⟩ i.isLt⟩
  invFun i := ⟨(π.symm ⟨i.val, by have := i.isLt; have := (π (Fin.last N)).isLt; omega⟩).val,
               front_symm π h
                 ⟨i.val, by have := i.isLt; have := (π (Fin.last N)).isLt; omega⟩ i.isLt⟩
  left_inv i := by apply Fin.ext; simp only [Fin.eta, Equiv.symm_apply_apply]
  right_inv i := by apply Fin.ext; simp only [Fin.eta, Equiv.apply_symm_apply]

def recon {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (L : ℕ) (hn : m + L = n) : Equiv.Perm
    (Fin n) :=
  (finCongr hn).permCongr (buildPerm m L ρ)

end MetaMathlibExt
