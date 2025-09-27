import sympy.sets.sets
import Lemma.Set.EqCeil.of.In_Ioc
open Set


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∈ Ioc 0 1) :
-- imply
  ⌈x⌉ = 1 := by
-- proof
  apply EqCeil.of.In_Ioc
  simp
  assumption


-- created on 2025-05-04
