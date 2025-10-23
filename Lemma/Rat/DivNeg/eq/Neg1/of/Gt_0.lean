import Lemma.Rat.DivNeg.eq.Neg1.of.Ne_0
import Lemma.Nat.Ne.of.Gt
open Nat Rat


@[main]
private lemma main
  [Preorder α]
  [DivisionRing α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  -x / x = -1 :=
-- proof
  (DivNeg.eq.Neg1.of.Ne_0 ∘ Ne.of.Gt) h


-- created on 2025-03-20
