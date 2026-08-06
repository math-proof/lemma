import Lemma.Set.EqCeil.of.In_Ioc
open Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {x : α}
-- given
  (h : x ∈ Ioc (z : α) (z + 1)) :
-- imply
  ⌈x⌉ = z + 1 := by
-- proof
  apply EqCeil.of.In_Ioc (z := z + 1)
  simpa using h


-- created on 2023-05-29
