import Lemma.Nat.Le.of.Lt
import Lemma.Algebra.EqAdd_Sub.of.Ge
open Algebra Nat


@[main]
private lemma main
  {n m : ℕ}
-- given
  (h : m < n) :
-- imply
  m + (n - m) = n := by
-- proof
  have h:= Le.of.Lt h

  apply EqAdd_Sub.of.Ge h


-- created on 2025-05-15
