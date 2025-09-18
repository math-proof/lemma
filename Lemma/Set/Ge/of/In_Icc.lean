import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma fin
  [Preorder α] [LocallyFiniteOrder α]
  {a b : α}
-- given
  (h : x ∈ Finset.Icc a b) :
-- imply
  x ≥ a := by
-- proof
  simp_all


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  x ≥ a :=
-- proof
  h.left


-- created on 2025-03-01
-- updated on 2025-05-18
