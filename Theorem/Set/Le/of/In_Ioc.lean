module

public import Theorem.Data.Set.Sets

public section

public theorem Set.Le.of.In_Ioc
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioc a b) :
-- imply
  x ≤ b :=
-- proof
  h₀.right


-- created on 2025-03-01
