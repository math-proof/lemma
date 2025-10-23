import sympy.sets.sets
import Lemma.Rat.EqCeil.is.Lt.Le
import Lemma.Set.Lt.of.In_Ioc
import Lemma.Set.Le.of.In_Ioc
open Set Rat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {x : α}
-- given
  (h : x ∈ Ioc (z - 1 : α) z) :
-- imply
  ⌈x⌉ = z := by
-- proof
  apply EqCeil.of.Lt.Le
  ·
    exact Lt.of.In_Ioc h
  ·
    exact Le.of.In_Ioc h


-- created on 2025-05-04
