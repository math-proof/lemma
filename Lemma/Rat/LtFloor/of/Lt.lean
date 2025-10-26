import Lemma.Rat.LeFloor
import Lemma.Nat.Lt.of.Le.Lt
open Nat Rat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  ⌊x⌋ < y := by
-- proof
  have h' := LeFloor x
  apply Lt.of.Le.Lt h' h


-- created on 2025-10-01
