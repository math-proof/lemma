module

public import Theorem.Data.Set.Sets

public section

public theorem Set.Lt.of.In_Ioc
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
