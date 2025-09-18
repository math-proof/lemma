import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [Preorder α] [LocallyFiniteOrder α]
-- given
  (i n : α) :
-- imply
  Ioc i n = Finset.Ioc i n := by
-- proof
  simp


-- created on 2025-05-18
