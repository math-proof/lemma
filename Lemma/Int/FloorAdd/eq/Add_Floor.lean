import Lemma.Algebra.Add
import Lemma.Int.FloorAdd.eq.AddFloor
open Algebra Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌊d + x⌋ = d + ⌊x⌋ := by
-- proof
  rw [Add.comm]
  rw [FloorAdd.eq.AddFloor]
  rw [Add.comm]


-- created on 2025-03-15
-- updated on 2025-10-08
