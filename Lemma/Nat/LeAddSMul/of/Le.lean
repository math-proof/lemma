import Lemma.Nat.LeMulS.of.Le
import Lemma.Nat.LeAddS.is.Le
open Nat


@[main, comm 1]
private lemma main
  {x y k : ℕ}
-- given
  (h : x ≤ y)
  (t : ℕ) :
-- imply
  k * x + t ≤ k * y + t := by
-- proof
  have := LeMulS.of.Le.left h k
  apply LeAddS.of.Le _ this


-- created on 2025-03-31
