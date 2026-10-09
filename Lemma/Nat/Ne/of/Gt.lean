import Lemma.Nat.Ne.of.Lt
open Nat


@[path]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≠ y :=
-- proof
  (Ne.of.Lt h).symm


-- created on 2021-09-06
-- updated on 2025-04-04
