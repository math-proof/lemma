import Lemma.Nat.EqMod.of.Lt
import Lemma.Nat.LtVal
open Nat


@[main]
private lemma main
-- given
  (j : Fin n) :
-- imply
  j % n = j := by
-- proof
  apply EqMod.of.Lt
  apply LtVal


-- created on 2025-07-07
