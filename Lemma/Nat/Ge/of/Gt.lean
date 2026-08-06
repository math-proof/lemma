import Lemma.Nat.Le.of.Lt
open Nat


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≥ y :=
-- proof
  Le.of.Lt h


-- created on 2018-06-28
-- updated on 2025-04-04
