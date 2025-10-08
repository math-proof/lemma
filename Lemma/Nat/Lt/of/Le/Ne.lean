import Lemma.Nat.Eq.of.Ge.Le
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h₀ : a ≠ b)
  (h₁ : a ≤ b) :
-- imply
  a < b := by
-- proof
  by_contra h
  simp at h
  have := Eq.of.Ge.Le h h₁
  contradiction


-- created on 2024-11-29
-- updated on 2025-06-18
