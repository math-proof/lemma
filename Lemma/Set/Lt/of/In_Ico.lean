import sympy.sets.sets
import sympy.Basic


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


@[main]
private lemma domain
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ico a b) :
-- imply
  a < b :=
-- proof
  lt_of_le_of_lt h₀.left h₀.right


-- created on 2021-03-12
-- updated on 2025-05-18
-- updated on 2026-09-27
