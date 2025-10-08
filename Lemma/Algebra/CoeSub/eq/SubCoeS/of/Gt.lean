import Lemma.Algebra.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.Ge.of.Gt
open Algebra Nat


@[main, comm]
private lemma main
  [AddGroupWithOne α]
  {a b : ℕ}
-- given
  (h : a > b) :
-- imply
  ((a - b : ℕ) : α) = a - b := by
-- proof
  apply CoeSub.eq.SubCoeS.of.Ge
  apply Ge.of.Gt h


-- created on 2025-05-04
