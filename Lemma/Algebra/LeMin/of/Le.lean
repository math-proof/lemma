import Lemma.Nat.LeMin
import Lemma.Algebra.Le.of.Le.Le
open Algebra Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a ≤ b) 
  (c : α):
-- imply
  a ⊓ c ≤ b := by
-- proof
  have h_le := LeMin.left a c
  apply Le.of.Le.Le h_le h


-- created on 2025-05-28
