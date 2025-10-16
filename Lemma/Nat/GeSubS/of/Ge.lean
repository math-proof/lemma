import Lemma.Algebra.LeSubS.is.Le
import Lemma.Nat.LeSubS.of.Le
open Algebra Nat


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h : x ≥ y)
  (z : ℕ) :
-- imply
  x - z ≥ y - z := by
-- proof
  apply LeSubS.of.Le h


-- created on 2025-10-16
