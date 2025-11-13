import Lemma.Nat.LeMulS.of.Le
import Lemma.Nat.LeAddS.is.Le
open Nat


@[main]
private lemma main
  {x y k : ℕ}
-- given
  (h : x ≥ y)
  (t : ℕ) :
-- imply
  k * x + t ≥ k * y + t := by
-- proof
  have := GeMulS.of.Ge.left h k
  apply GeAddS.of.Ge _ this


-- created on 2025-03-31
