import stdlib.Slice
import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.Int.EqSign_1.of.Gt_0
open Nat Int


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n ≥ 0) :
-- imply
  (1 - sign n) / 2 = 0 := by
-- proof
  by_cases h_n : n = 0
  ·
    subst n
    simp
  ·
    have h_n := Gt.of.Ge.Ne h h_n
    have := EqSign_1.of.Gt_0 h_n
    rw [this]
    simp


-- created on 2025-06-26
