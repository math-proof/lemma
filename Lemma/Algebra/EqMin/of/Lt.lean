import Lemma.Algebra.Le.of.Lt
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a ⊓ b = a := by
-- proof
  simp [Le.of.Lt h]


-- created on 2025-05-17
