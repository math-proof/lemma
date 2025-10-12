import Lemma.Nat.EqMin.of.Le
import Lemma.Algebra.LeAdd_1
open Algebra Nat


@[main]
private lemma main
-- given
  (i : Fin n) :
-- imply
  (i.val + 1) ⊓ n = i.val + 1 := by
-- proof
  apply EqMin.of.Le
  apply LeAdd_1


-- created on 2025-07-18
