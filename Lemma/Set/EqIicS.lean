import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [Preorder α] [LocallyFiniteOrderBot α]
-- given
  (i : α) :
-- imply
  Iic i = Finset.Iic i := by
-- proof
  simp


-- created on 2025-05-18
