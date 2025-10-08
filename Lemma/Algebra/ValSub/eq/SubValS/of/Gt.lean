import Lemma.Algebra.ValSub.eq.SubValS.of.Ge
import Lemma.Nat.Ge.of.Gt
open Algebra Nat


@[main]
private lemma main
  {i j : Fin n}
-- given
  (h : i > j) :
-- imply
  (i - j).val = i.val - j.val := by
-- proof
  apply ValSub.eq.SubValS.of.Ge
  apply Ge.of.Gt h


-- created on 2025-06-21
