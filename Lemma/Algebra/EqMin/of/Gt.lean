import Lemma.Algebra.Ge.of.Gt
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a ⊓ b = b := by
-- proof
  simp [h]
  apply Ge.of.Gt h


-- created on 2025-06-07
