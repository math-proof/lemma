import Lemma.Nat.GtAddS.is.Gt
import Lemma.Algebra.EqAdd0
open Algebra Nat


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h : a > 0) :
-- imply
  b < a + b := by
-- proof
  have := GtAddS.of.Gt b h
  rwa [EqAdd0] at this


-- created on 2025-05-24
-- updated on 2025-10-16
