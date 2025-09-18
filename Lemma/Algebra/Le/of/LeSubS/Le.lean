import Lemma.Algebra.EqAddSub.of.Ge
open Algebra


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
  rw [EqAddSub.of.Ge h₀] at h₁
  assumption


-- created on 2025-05-14
