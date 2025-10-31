import Lemma.Nat.Add
open Nat


@[main, comm]
private lemma main
  {a b c : ℕ}
-- given
  (h : a ≥ c) :
-- imply
  a + b - c = a - c + b := by
-- proof
  rw [Add.comm]
  rw [Nat.add_sub_assoc h]
  rw [Add.comm]


-- created on 2025-03-31
