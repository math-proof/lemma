import Lemma.Nat.GeMulS.of.Ge
import Lemma.Nat.LeSubS.of.Le
open Nat


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h : x ≥ y)
  (k t : ℕ) :
-- imply
  k * x - t ≥ k * y - t := by
-- proof
  have := GeMulS.of.Ge h k
  apply LeSubS.of.Le this


-- created on 2025-03-31
