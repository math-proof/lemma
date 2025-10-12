import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.Ge.of.Gt
open Nat


@[main]
private lemma main
  {n m : ℕ}
-- given
  (h : n > m) :
-- imply
  m + (n - m) = n := by
-- proof
  apply EqAdd_Sub.of.Ge
  apply Ge.of.Gt h


-- created on 2025-06-21
