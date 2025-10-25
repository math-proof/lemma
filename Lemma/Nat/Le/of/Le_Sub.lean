import Lemma.Nat.LeSub
import Lemma.Algebra.Le.of.Le.Le
open Algebra Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : a ≤ b - c) :
-- imply
  a ≤ b := by
-- proof
  have := LeSub b c
  apply Le.of.Le.Le h this


-- created on 2025-06-21
