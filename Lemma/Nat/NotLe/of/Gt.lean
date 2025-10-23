import Lemma.Nat.NotGe.of.Lt
open Nat


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  ¬a ≤ b := by
-- proof
  apply NotGe.of.Lt h


-- created on 2025-03-29
-- updated on 2025-07-19
