import Lemma.Nat.LeMulS.of.Le
import Lemma.Nat.Ge_1.of.Gt_0
open Nat


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n > 0)
  (m : ℕ) :
-- imply
  m * n ≥ m := calc
-- proof
  _ = m * 1 := by simp
  _ ≤ m * n := LeMulS.of.Le.left (Ge_1.of.Gt_0 h) m


-- created on 2026-08-02
