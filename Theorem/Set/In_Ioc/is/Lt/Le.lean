module

public import Mathlib
public import Theorem.Data.Set.Sets
public import Initialize.Tactic.Attr.Basic

public section


@[comm, mp, mpr]
public theorem Set.In_Ioc.is.Lt.Le
  [Preorder α]
-- given
  (a b : α) :
-- imply
  x ∈ Ioc a b ↔ a < x ∧ x ≤ b := by
-- proof
  rfl



public theorem Set.In_Ioc.of.Lt.Le
  [Preorder α]
  {x a b : α}
  (h₀ : a < x)
  (h₁ : x ≤ b) :
  x ∈ Ioc a b :=
  (Set.In_Ioc.is.Lt.Le a b).mpr ⟨h₀, h₁⟩

-- created on 2025-03-02
