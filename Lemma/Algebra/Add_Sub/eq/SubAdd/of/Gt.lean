import Lemma.Algebra.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Nat.Ge.of.Gt
open Algebra Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : b > c) :
-- imply
  a + (b - c) = a + b - c := by
-- proof
  apply Add_Sub.eq.SubAdd.of.Ge
  apply Ge.of.Gt h


-- created on 2025-06-21
