import Lemma.Nat.LtSub.of.Lt
open Nat


@[main]
private lemma main
-- given
  (j : Fin n)
  (i : ℕ) :
-- imply
  j - i < n := by
-- proof
  apply LtSub.of.Lt
  apply j.isLt


-- created on 2025-06-21
