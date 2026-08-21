import Lemma.Nat.Add
import Lemma.Int.CeilAdd.eq.AddCeil
open Nat Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌈d + x⌉ = d + ⌈x⌉ := by
-- proof
  rw [Add.comm]
  rw [CeilAdd.eq.AddCeil]
  rw [Add.comm]


-- created on 2025-03-15
