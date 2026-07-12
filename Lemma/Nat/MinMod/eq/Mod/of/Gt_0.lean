import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.LeMod.of.Gt_0
open Nat


@[main]
private lemma main
-- given
  (h_n : n > 0)
  (k : ℕ) :
-- imply
  k % n ⊓ n = k % n := by
-- proof
  rw [EqMin.of.Le]
  apply LeMod.of.Gt_0 h_n


-- created on 2026-07-12
