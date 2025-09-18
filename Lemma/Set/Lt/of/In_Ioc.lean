import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma fin
  [Preorder α] [LocallyFiniteOrder α]
  {a b : α}
-- given
  (h : x ∈ Finset.Ioc a b) :
-- imply
  a < x := by
-- proof
  simp_all


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : x ∈ Ioc a b) :
-- imply
  a < x :=
-- proof
  h.left


-- created on 2025-03-01
-- updated on 2025-05-18
