module
public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm, mp, mpr]
public theorem List.Cons.is.Eq.Eq
-- given
  (a b : List α) :
-- imply
  a₀ :: a = b₀ :: b ↔ a₀ = b₀ ∧ a = b := by
-- proof
  aesop


-- created on 2025-10-10
