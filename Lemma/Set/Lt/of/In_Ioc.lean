import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
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
-- updated on 2026-10-26
