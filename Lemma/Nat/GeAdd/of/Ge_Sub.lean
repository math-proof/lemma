import Lemma.Algebra.GeAddS.is.Ge
open Algebra


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : a ≥ c - b) :
-- imply
  a + b ≥ c := by
-- proof
  have h := GeAddS.of.Ge b h
  simp at h
  exact h


-- created on 2025-05-04
-- updated on 2025-10-16
