import Lemma.Algebra.GeMax
import Lemma.Algebra.Ge.of.Ge.Ge
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a ≥ b) 
  (c : α) :
-- imply
  a ⊔ c ≥ b := by
-- proof
  have h_ge := GeMax.left a c
  apply Ge.of.Ge.Ge h_ge h


-- created on 2025-05-28
