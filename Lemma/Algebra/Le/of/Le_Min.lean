import Lemma.Algebra.LeMin
import Lemma.Algebra.Le.of.Le.Le
open Algebra


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : x ≤ a ⊓ b) :
-- imply
  x ≤ b := by
-- proof
  have h_le := LeMin a b
  apply Le.of.Le.Le h h_le


-- created on 2025-05-31
