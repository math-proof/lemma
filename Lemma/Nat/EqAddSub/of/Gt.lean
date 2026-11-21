import Lemma.Nat.EqAddSub.of.Ge
import Theorem.Nat.Ge.of.Gt
import Initialize.Tactic.Attr.Basic
open Nat


@[path]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : b > a) :
-- imply
  b - a + a = b := by
-- proof
  apply EqAddSub.of.Ge
  apply Ge.of.Gt h


-- created on 2025-06-18
-- updated on 2026-11-20
