/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push
import Def.Combinatorics.Enumerative.FibonacciPAPAvoidance.Part3


namespace MetaMathlibExt

lemma recon_val {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (L : ℕ) (hn : m + L = n) (x : Fin n) :
    (recon ρ L hn x).val = (buildPerm m L ρ ⟨x.val, Nat.lt_of_lt_of_eq x.2 hn.symm⟩).val := by
  simp only [recon, Equiv.permCongr_apply, finCongr_apply, finCongr_symm, Fin.val_cast]
  rfl

lemma isGood_recon {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (hρ : IsGood m ρ) (L : ℕ)
    (hn : m + L = n)
    (hL : L % 2 = 1) : IsGood n (recon ρ L hn) := by
  subst hn
  simp only [recon, finCongr_refl]
  exact buildPerm_good ρ hρ hL

lemma recon_lt {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (L : ℕ) (hn : m + L = n) (x : Fin n)
    (hx : x.val < m) : (recon ρ L hn x).val = (ρ ⟨x.val, hx⟩).val := by
  rw [recon_val]
  exact buildPerm_lt ρ ⟨x.val, Nat.lt_of_lt_of_eq x.2 hn.symm⟩ hx

lemma recon_ge {m n : ℕ} (ρ : Equiv.Perm (Fin m)) (L : ℕ) (hn : m + L = n) (x : Fin n)
    (hx : m ≤ x.val) : (recon ρ L hn x).val = 2*m + L - 1 - x.val := by
  rw [recon_val]
  exact buildPerm_ge ρ ⟨x.val, Nat.lt_of_lt_of_eq x.2 hn.symm⟩ hx

lemma recon_front {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
    π = recon (frontPerm π h) (N + 1 - (π (Fin.last N)).val)
          (by have := Nat.lt_succ_iff.mp (Fin.is_lt (π (Fin.last N))); omega) := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  by_cases hx : x.val < (π (Fin.last N)).val
  · rw [recon_lt _ _ _ x hx, frontPerm_apply π h
      ⟨x.val, by have := x.isLt; omega⟩ (by have := x.isLt; omega)]
  · have hxge : (π (Fin.last N)).val ≤ x.val := by omega
    have hcN : (π (Fin.last N)).val ≤ N := Nat.lt_succ_iff.mp (Fin.is_lt _)
    have hxN : x.val ≤ N := Nat.lt_succ_iff.mp x.isLt
    rw [recon_ge _ _ _ x hxge, block_val π h x hxge]
    omega

end MetaMathlibExt
