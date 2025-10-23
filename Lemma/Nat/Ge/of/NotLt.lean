import Lemma.Nat.NotGt.is.Le
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : ¬a < b) :
-- imply
  a ≥ b :=
-- proof
  Le.of.NotGt h


-- created on 2025-03-23
