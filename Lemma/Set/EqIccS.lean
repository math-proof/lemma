import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Preorder α] [LocallyFiniteOrder α]
-- given
  (i n : α) :
-- imply
  Icc i n = Finset.Icc i n := by
-- proof
  simp


-- created on 2025-05-18
