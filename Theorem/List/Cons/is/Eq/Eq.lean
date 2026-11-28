module
public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[path, comm, mp, mpr]
private lemma main
-- given
  (a b : List α) :
-- imply
  a₀ :: a = b₀ :: b ↔ a₀ = b₀ ∧ a = b := by
-- proof
  aesop


-- created on 2025-10-10
