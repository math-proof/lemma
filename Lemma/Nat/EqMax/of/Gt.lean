import Lemma.Nat.Ge.of.Gt
import Lemma.Nat.EqMax.of.Ge
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a ⊔ b = a := 
-- proof
  EqMax.of.Ge (Ge.of.Gt h)


-- created on 2025-05-17
-- updated on 2025-10-12
