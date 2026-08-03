import Lemma.Nat.Le.ou.Gt
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {x y : α}
-- given
  (h : x ≥ y)
  (z : α) :
-- imply
  x > z ∨ (x ≤ z ∧ x ≥ y) := by
-- proof
  obtain h' | h' := Le.ou.Gt x z
  ·
    exact Or.inr ⟨h', h⟩
  ·
    exact Or.inl h'


-- created on 2026-08-03
