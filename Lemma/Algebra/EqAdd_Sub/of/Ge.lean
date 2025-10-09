import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Add
open Nat


@[main]
private lemma main
  {n m : ℕ}
-- given
  (h : n ≥ m) :
-- imply
  m + (n - m) = n := by
-- proof
  rw [Add.comm]
  apply EqAddSub.of.Ge h


-- created on 2025-05-09
-- updated on 2025-06-08
