import Lemma.Nat.GeMulS.of.Ge
import Lemma.Nat.GeAddS.is.Ge
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
  have := GeMulS.of.Ge h k
  apply GeAddS.of.Ge _ this


-- created on 2025-03-31
