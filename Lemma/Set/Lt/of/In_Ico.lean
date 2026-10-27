import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ico a b) :
-- imply
  x < b :=
-- proof
  h₀.right

@[path]
private lemma domain
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ico a b) :
-- imply
  a < b :=
-- proof
  lt_of_le_of_lt h₀.left h₀.right


-- created on 2023-11-12
-- updated on 2026-10-26
-- updated on 2026-10-24
