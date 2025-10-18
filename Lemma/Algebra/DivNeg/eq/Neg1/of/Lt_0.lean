import Lemma.Nat.Ne.of.Lt
import Lemma.Algebra.DivNeg.eq.Neg1.of.Ne_0
open Algebra Nat


@[main]
private lemma main
  [Preorder α]
  [DivisionRing α]
  {x : α}
-- given
  (h : x < 0) :
-- imply
  -x / x = -1 :=
-- proof
  (DivNeg.eq.Neg1.of.Ne_0 ∘ Ne.of.Lt) h


-- created on 2025-03-20
