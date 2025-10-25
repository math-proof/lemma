import Lemma.Nat.NotGt.of.Lt
open Nat


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  ¬a < b :=
-- proof
  NotGt.of.Lt h


-- created on 2025-03-30
