import Lemma.Algebra.Ge.of.Ge.Ge
open Algebra


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h : a ≥ b)
  (c : ℕ) :
-- imply
  a + c ≥ b := by
-- proof
  have h' : a + c ≥ a := by 
    simp
  apply Ge.of.Ge.Ge h' h


-- created on 2025-05-28
