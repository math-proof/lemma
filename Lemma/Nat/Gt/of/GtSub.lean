import Lemma.Nat.Gt_0.of.Gt
import Lemma.Nat.Sub.gt.Zero.is.Gt
open Nat


@[path]
private lemma main
  {a b c : ℕ}
-- given
  (h : a - b > c) :
-- imply
  a > b := by
-- proof
  have h := Gt_0.of.Gt h
  apply Gt.of.Sub.gt.Zero h


-- created on 2025-05-04
