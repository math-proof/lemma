import Lemma.Algebra.EqAddSub.of.Ge
open Algebra


@[main]
private lemma main
-- given
  (h : z ≤ y)
  (x : ℕ) :
-- imply
  x - z ≤ y - z ↔ x ≤ y := by
-- proof
  simp
  rw [EqAddSub.of.Ge h]


-- created on 2025-05-14
