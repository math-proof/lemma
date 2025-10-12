import Lemma.Nat.Ge.of.Gt
import Lemma.Nat.EqMin.of.Ge
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a ⊓ b = b := 
-- proof
  EqMin.of.Ge (Ge.of.Gt h)


-- created on 2025-06-07
-- updated on 2025-10-12
