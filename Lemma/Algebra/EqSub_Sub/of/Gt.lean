import Lemma.Algebra.EqSub_Sub.of.Ge
import Lemma.Nat.Ge.of.Gt
open Algebra Nat


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h : a > b) :
-- imply
  a - (a - b) = b := by
-- proof
  apply EqSub_Sub.of.Ge
  apply Ge.of.Gt h


-- created on 2025-06-21
