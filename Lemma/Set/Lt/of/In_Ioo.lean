import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
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
-- updated on 2026-10-26
