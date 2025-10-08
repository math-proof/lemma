import Lemma.Algebra.Add
import Lemma.Nat.FloorAdd.eq.AddFloor
open Algebra Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℕ} :
-- imply
  ⌊d + x⌋ = d + ⌊x⌋ := by
-- proof
  rw [Add.comm]
  rw [FloorAdd.eq.AddFloor]
  rw [Add.comm]


-- created on 2025-10-08
