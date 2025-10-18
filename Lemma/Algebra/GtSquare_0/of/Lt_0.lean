import sympy.core.power
import Lemma.Algebra.GtSquare_0.of.Ne_0
import Lemma.Nat.Ne.of.Lt
open Algebra Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a : α}
-- given
  (h : a < 0) :
-- imply
  a² > 0 := by
-- proof
  have := Ne.of.Lt h
  apply GtSquare_0.of.Ne_0 this


-- created on 2025-04-06
