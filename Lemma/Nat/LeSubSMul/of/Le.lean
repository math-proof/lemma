import Lemma.Nat.LeMulS.of.Le
import Lemma.Nat.LeSubS.of.Le
open Nat


@[main, comm 1]
private lemma main
  {x y : ℕ}
-- given
  (h : x ≤ y)
  (k t : ℕ) :
-- imply
  k * x - t ≤ k * y - t := by
-- proof
  have := LeMulS.of.Le.left h k
  apply LeSubS.of.Le this


-- created on 2025-03-31
