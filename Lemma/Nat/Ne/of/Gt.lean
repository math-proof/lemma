import Lemma.Nat.Ne.of.Lt
open Nat


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≠ y :=
-- proof
  (Ne.of.Lt h).symm


-- created on 2024-07-01
-- updated on 2025-04-04
