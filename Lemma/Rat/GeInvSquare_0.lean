import Lemma.Int.GeSquare_0
import Lemma.Rat.GeInv_0.is.Ge_0
open Rat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a : α) :
-- imply
  (a²)⁻¹ ≥ 0 := by
-- proof
  apply GeInv_0.of.Ge_0
  apply GeSquare_0


-- created on 2025-12-20
