import Lemma.Nat.LeMin
import Lemma.Nat.Ge.of.Ge.Ge
open Nat


@[main]
private lemma main
  [LinearOrder α]
-- given
  (h : c ≥ a)
  (b : α) :
-- imply
  c ≥ a ⊓ b := by
-- proof
  have := LeMin.left a b
  apply Ge.of.Ge.Ge h this


-- created on 2025-05-14
