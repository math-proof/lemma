import Lemma.Nat.Add
import Lemma.Nat.SubAdd.eq.Add_Sub.of.Ge
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
  rw [SubAdd.eq.Add_Sub.of.Ge h]
  rw [Add.comm]


-- created on 2025-03-31
