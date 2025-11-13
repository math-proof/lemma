import Lemma.Int.EqSign_1.of.Gt_0
import Lemma.Nat.LeAdd_1.of.Lt
open Nat Int


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d > 0) :
-- imply
  sign d ≤ d := by
-- proof
  have := EqSign_1.of.Gt_0 h
  rw [this]
  have := Ge_Add_1.of.Gt h
  simp_all


-- created on 2025-03-30
