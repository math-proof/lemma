import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.EqAddSub.of.Ge
open Nat


@[main, comm 2]
private lemma left
  {x a b : ℕ}
-- given
  (h₀ : a ≥ b)
  (h₁ : b + x ≠ a) :
-- imply
  x ≠ a - b := by
-- proof
  by_contra h'
  rw [h'] at h₁
  rw [EqAdd_Sub.of.Ge (by assumption)] at h₁
  contradiction


@[main, comm 2]
private lemma main
  {x a b : ℕ}
-- given
  (h₀ : a ≥ b)
  (h₁ : x + b ≠ a) :
-- imply
  x ≠ a - b := by
-- proof
  by_contra h'
  rw [h'] at h₁
  rw [EqAddSub.of.Ge (by assumption)] at h₁
  contradiction


-- created on 2025-06-11
