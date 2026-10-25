/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean -/

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Push
import Theorem.Combinatorics.Enumerative.FibonacciPAPAvoidance.Part4


namespace MetaMathlibExt

def fiberEquiv {N : ℕ} (b : Fin (N + 1)) (hb : (N - b.val) % 2 = 0) :
    {π : Equiv.Perm (Fin (N+1)) // IsGood (N+1) π ∧ π (Fin.last N) = b} ≃
      {ρ : Equiv.Perm (Fin b.val) // IsGood b.val ρ} where
  toFun π := ⟨frontFixed b π.1 π.2.1 π.2.2, frontFixed_good b π.1 π.2.1 π.2.2⟩
  invFun ρ := ⟨recon ρ.1 (N + 1 - b.val) (by have := Nat.lt_succ_iff.mp b.isLt; omega),
    ⟨isGood_recon ρ.1 ρ.2 (N + 1 - b.val) (by have := Nat.lt_succ_iff.mp b.isLt; omega)
        (by have := Nat.lt_succ_iff.mp b.isLt; omega),
      recon_last b ρ.1 (by have := Nat.lt_succ_iff.mp b.isLt; omega)⟩⟩
  left_inv π := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Fin.ext
    have hπ := π.2.2
    have hbN : b.val ≤ N := Nat.lt_succ_iff.mp b.isLt
    by_cases hx : x.val < b.val
    · rw [recon_lt _ _ _ x hx,
        frontFixed_apply b π.1 π.2.1 hπ
            ⟨x.val, by have := x.isLt; omega⟩ (by have := x.isLt; omega)]
    · have hxge : b.val ≤ x.val := by omega
      have hxN : x.val ≤ N := Nat.lt_succ_iff.mp x.isLt
      have hlast : (π.1 (Fin.last N)).val = b.val := by rw [hπ]
      rw [recon_ge _ _ _ x hxge, block_val π.1 π.2.1 x (by rw [hlast]; omega), hlast]
      omega
  right_inv ρ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Fin.ext
    have hbN : b.val ≤ N := Nat.lt_succ_iff.mp b.isLt
    rw [frontFixed_apply b _ _ _ i (by have := i.isLt; omega),
        recon_lt _ _ _ ⟨i.val, by have := i.isLt; omega⟩ (by have := i.isLt; exact i.isLt)]

end MetaMathlibExt
