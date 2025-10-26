import Lemma.Rat.DivMulS.eq.Div.of.Ne_0
import Lemma.Nat.Ne.of.Gt
open Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {n d a : α}
-- given
  (h : a > 0) :
-- imply
  (n * a) / (d * a) = n / d := by
-- proof
  have := Ne.of.Gt h
  apply DivMulS.eq.Div.of.Ne_0 this


-- created on 2025-04-06
