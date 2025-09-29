import sympy.sets.sets
import sympy.Basic


@[main]
private lemma fin
  [Preorder α] [LocallyFiniteOrder α]
  {a b : α}
-- given
  (h₀ : x ∈ Finset.Ioo a b) :
-- imply
  x < b := by
-- proof
  simp_all


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioo a b) :
-- imply
  x < b :=
-- proof
  h₀.right


-- created on 2025-03-01
-- updated on 2025-05-18
