import Lemma.Nat.EqAddSub.of.Ge
open Nat


@[main]
private lemma main
  {x y z : ℕ}
-- given
  (h₀ : z ≤ y)
  (h₁ : x - z ≤ y - z) :
-- imply
  x ≤ y := by
-- proof
  simp at h₁
  rwa [EqAddSub.of.Ge h₀] at h₁


-- created on 2025-05-14
