import Lemma.Algebra.EqAdd_Sub.of.Ge
import Lemma.Algebra.Ge.of.Gt
open Algebra


@[main]
private lemma main
  {n m : ℕ}
-- given
  (h : n > m) :
-- imply
  m + (n - m) = n := by
-- proof
  apply EqAdd_Sub.of.Ge
  apply Ge.of.Gt h


-- created on 2025-06-21
