import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α] [LocallyFiniteOrder α]
-- given
  (i n : α) :
-- imply
  Ioo i n = Finset.Ioo i n := by
-- proof
  simp


-- created on 2025-05-18
