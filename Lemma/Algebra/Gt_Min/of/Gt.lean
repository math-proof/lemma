import Lemma.Nat.LeMin
import Lemma.Algebra.Gt.of.Gt.Ge
open Algebra Nat


@[main]
private lemma main
  [LinearOrder α]
-- given
  (h : c > a)
  (b : α) :
-- imply
  c > a ⊓ b := by
-- proof
  have := LeMin.left a b
  apply Gt.of.Gt.Ge h this


-- created on 2025-05-14
