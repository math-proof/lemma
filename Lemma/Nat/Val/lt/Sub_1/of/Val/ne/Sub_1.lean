import Lemma.Nat.Le_Sub_1
import Lemma.Nat.Lt.of.Le.Ne
open Nat


@[main]
private lemma main
  {i : Fin n}
-- given
  (h : i.val ≠ n - 1) :
-- imply
  i.val < n - 1 := by
-- proof
  have := Le_Sub_1 i
  apply Lt.of.Le.Ne h this


-- created on 2025-06-18
