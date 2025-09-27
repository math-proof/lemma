import Lemma.Algebra.Add
import Lemma.Algebra.FloorAdd.eq.AddFloor
open Algebra


@[main]
private lemma nat
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℕ} :
-- imply
  ⌊d + x⌋ = d + ⌊x⌋ := by
-- proof
  rw [Add.comm]
  rw [FloorAdd.eq.AddFloor.nat]
  rw [Add.comm]


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
-- updated on 2025-04-04
