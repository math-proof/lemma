import Lemma.Nat.Ge.of.Ge.Ge
open Nat


@[main]
private lemma main
  {z : ℤ}
  {n : ℕ}
-- given
  (h : z ≥ n) :
-- imply
  z.toNat ≥ n := by
-- proof
  have hz := Ge.of.Ge.Ge h (show (n : ℤ) ≥ 0 by simp)
  simp [Int.le_toNat hz]
  assumption


-- created on 2025-05-12
