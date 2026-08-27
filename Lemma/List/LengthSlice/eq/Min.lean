import stdlib.Slice
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
open Nat


@[main]
private lemma main
-- given
  (n m : ℕ) :
-- imply
  (⟨0, n, 1⟩ : Slice).length m = n ⊓ m := by
-- proof
  simp [Slice.length, EqAdd_Mul_DivSub1Sign_2 m n, EqAdd_Mul_DivSub1Sign_2.zero m]
  convert Int.toNat_natCast (n ⊓ m)
  rcases Nat.le_total n m with h | h <;> simp [h]


-- created on 2025-08-04
-- updated on 2026-08-24
