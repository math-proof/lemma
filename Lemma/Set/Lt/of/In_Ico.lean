import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma fin
  [Preorder α] [LocallyFiniteOrder α]
  {a b : α}
-- given
  (h₀ : x ∈ Finset.Ico a b) :
-- imply
  x < b := by
-- proof
  simp_all


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ico a b) :
-- imply
  x < b :=
-- proof
  h₀.right


-- created on 2025-03-01
-- updated on 2025-05-18
