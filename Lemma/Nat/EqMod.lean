import Theorem.Nat.EqMod.of.Lt
open Nat


@[path]
private lemma main
-- given
  (j : Fin n) :
-- imply
  j % n = j := by
-- proof
  apply EqMod.of.Lt
  simp


-- created on 2025-07-07
-- updated on 2026-11-22
