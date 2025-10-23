import Lemma.Nat.Eq.of.Ge.Le
import Lemma.Nat.Le.of.Lt
import Lemma.Nat.Ne.of.Lt
open Nat


@[main, comm, mp, mpr]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  a > b ↔ a ≥ b ∧ a ≠ b := by
-- proof
  constructor <;>
    intro h
  .
    constructor
    ·
      exact Le.of.Lt h
    ·
      apply Ne.symm (Ne.of.Lt h)
  .
    let ⟨h₀, h₁⟩ := h
    by_contra h
    simp at h
    have := Eq.of.Ge.Le h₀ h
    contradiction


-- created on 2025-04-18
