import Lemma.Nat.Ge_0
import Lemma.Nat.Eq.of.Le.Le
open Nat


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n ≤ 0) :
-- imply
  n = 0 := by
-- proof
  have := Ge_0 n
  apply Eq.of.Le.Le h this


-- created on 2018-03-15
