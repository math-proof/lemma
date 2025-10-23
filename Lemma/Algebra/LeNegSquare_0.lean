import Lemma.Int.GeSquare_0
import Lemma.Algebra.LeNeg_0.of.Ge_0
open Algebra Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a : α} :
-- imply
  -a² ≤ 0 := by
-- proof
  have h := GeSquare_0 (a := a)
  apply LeNeg_0.of.Ge_0 h


-- created on 2024-11-29
