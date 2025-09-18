import Lemma.Algebra.GeAddS.is.Ge
open Algebra


@[main]
private lemma nat
  {a b c : ℕ}
-- given
  (h : a ≥ c - b) :
-- imply
  a + b ≥ c := by
-- proof
  have h := GeAddS.of.Ge b h
  simp at h
  exact h


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a ≥ c - b) :
-- imply
  a + b ≥ c := by
-- proof
  have h := GeAddS.of.Ge b h
  simp at h
  exact h


-- created on 2025-05-04
