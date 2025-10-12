import Lemma.Nat.Le.of.Lt
import Lemma.Nat.EqMax.of.Le
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a ⊔ b = b := 
-- proof
  EqMax.of.Le (Le.of.Lt h)


-- created on 2025-06-07
-- updated on 2025-10-12
