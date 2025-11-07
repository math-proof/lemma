import Lemma.Nat.NeCoe_0.is.Ne_0
open Nat


@[main, comm]
private lemma main
  [DivisionSemiring K]
  [CharZero K]
  {m n : ℕ}
-- given
  (hnm : n ∣ m)
  (hn : n ≠ 0) :
-- imply
  (m / n : ℕ) = (m / n : K) := by
-- proof
  apply Nat.cast_div hnm
  apply NeCoe_0.of.Ne_0 hn


-- created on 2025-11-07
