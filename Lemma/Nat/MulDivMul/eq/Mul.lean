import Lemma.Nat.EqDivMul.of.Ne_0
open Nat


@[main]
private lemma main
-- given
  (n m : ℕ) :
-- imply
  n * m / m * m = n * m := by
-- proof
  simp
  if h_0 : m = 0 then
    right
    assumption
  else
    left
    rwa [EqDivMul.of.Ne_0]


-- created on 2026-07-10
