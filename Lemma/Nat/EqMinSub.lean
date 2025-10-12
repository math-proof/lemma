import Lemma.Nat.EqMin.of.Le
open Nat


@[main]
private lemma main
-- given
  (a b : ℕ) :
-- imply
  (a - b) ⊓ a = a - b := by
-- proof
  rw [EqMin.of.Le]
  omega


-- created on 2025-10-12
