/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push
import Def.Combinatorics.Enumerative.FibonacciPAPAvoidance.Part4


namespace MetaMathlibExt

lemma frontFixed_apply {N : ℕ} (b : Fin (N + 1)) (π : Equiv.Perm (Fin (N + 1)))
    (h : IsGood (N + 1) π)
    (hπ : π (Fin.last N) = b) (i : Fin b.val) (hlt : i.val < N + 1) :
    (frontFixed b π h hπ i).val = (π ⟨i.val, hlt⟩).val := rfl

lemma frontFixed_good {N : ℕ} (b : Fin (N + 1)) (π : Equiv.Perm (Fin (N + 1)))
    (h : IsGood (N + 1) π)
    (hπ : π (Fin.last N) = b) : IsGood b.val (frontFixed b π h hπ) := by
  have hbN : b.val ≤ N := Nat.lt_succ_iff.mp b.isLt
  obtain ⟨hpar, h312, h231⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hlt : i.val < N + 1 := by have := i.isLt; omega
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ i hlt]
    exact hpar ⟨i.val, hlt⟩
  · intro i j k hij hjk ⟨hjk', hki'⟩
    have hli : i.val < N + 1 := by have := i.isLt; omega
    have hlj : j.val < N + 1 := by have := j.isLt; omega
    have hlk : k.val < N + 1 := by have := k.isLt; omega
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ j hlj, frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ
        k hlk] at hjk'
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ k hlk, frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ
        i hli] at hki'
    exact h312 ⟨i.val, hli⟩ ⟨j.val, hlj⟩ ⟨k.val, hlk⟩ hij hjk ⟨hjk', hki'⟩
  · intro i j k hij hjk ⟨hki', hij'⟩
    have hli : i.val < N + 1 := by have := i.isLt; omega
    have hlj : j.val < N + 1 := by have := j.isLt; omega
    have hlk : k.val < N + 1 := by have := k.isLt; omega
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ k hlk, frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ
        i hli] at hki'
    rw [frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ i hli, frontFixed_apply b π ⟨hpar, h312, h231⟩ hπ
        j hlj] at hij'
    exact h231 ⟨i.val, hli⟩ ⟨j.val, hlj⟩ ⟨k.val, hlk⟩ hij hjk ⟨hki', hij'⟩

lemma recon_last {N : ℕ} (b : Fin (N + 1)) (ρ : Equiv.Perm (Fin b.val))
    (hn : b.val + (N + 1 - b.val) = N + 1) :
    recon ρ (N + 1 - b.val) hn (Fin.last N) = b := by
  apply Fin.ext
  have hbN : b.val ≤ N := Nat.lt_succ_iff.mp b.isLt
  rw [recon_ge _ _ _ (Fin.last N) (by rw [Fin.val_last]; omega)]
  rw [Fin.val_last]
  omega

end MetaMathlibExt
