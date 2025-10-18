import Lemma.Nat.Ne.of.Gt
import Lemma.Rat.Div.eq.One.of.Ne_0
open Rat Nat


@[main]
private lemma main
  [Preorder α]
  [GroupWithZero α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  x / x = 1 :=
-- proof
  (Div.eq.One.of.Ne_0 ∘ Ne.of.Gt) h


-- created on 2024-11-25
