import Lemma.Nat.EqAddS.is.Eq
import Lemma.Algebra.SubSquareS.eq.MulAdd__Sub
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
import Lemma.Nat.EqSubS.of.Eq
open Algebra Nat


@[main]
private lemma main
  [Field α]
  {x c : α}
-- given
  (h : x² = c²) :
-- imply
  x = c ∨ x = -c := by
-- proof
  have h := EqSubS.of.Eq h c²
  simp at h
  rw [SubSquareS.eq.MulAdd__Sub] at h
  have h := OrEqS_0.of.Mul.eq.Zero h
  cases h with
  | inl h =>
    have h := EqSubS.of.Eq h c
    simp at h
    exact Or.inr h
  | inr h =>
    have h := EqAddS.of.Eq c h
    simp at h
    exact Or.inl h


-- created on 2024-07-01
-- updated on 2025-04-05
