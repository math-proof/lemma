import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [Preorder α] [LocallyFiniteOrderTop α]
-- given
  (i : α) :
-- imply
  Ioi i = Finset.Ioi i := by
-- proof
  simp


-- created on 2025-05-18
