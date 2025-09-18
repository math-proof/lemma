import Lemma.Algebra.Eq.of.Ge.Le
import Lemma.Algebra.Le.of.Lt
import Lemma.Algebra.Ne.of.Lt
open Algebra


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
