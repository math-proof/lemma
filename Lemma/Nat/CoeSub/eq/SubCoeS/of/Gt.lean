import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.Ge.of.Gt
open Nat


@[main, comm]
private lemma main
  [AddGroupWithOne Z]
  {a b : ℕ}
-- given
  (h : a > b) :
-- imply
  ((a - b : ℕ) : Z) = a - b := by
-- proof
  apply CoeSub.eq.SubCoeS.of.Ge
  apply Ge.of.Gt h


-- created on 2025-05-04
