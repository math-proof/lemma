import Lemma.Nat.Le.of.Lt
import Lemma.Nat.EqMin.of.Le
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a ⊓ b = a :=
-- proof
  EqMin.of.Le (Le.of.Lt h)


-- created on 2025-05-17
-- updated on 2025-10-12
