import Lemma.Algebra.EqNegS.is.Eq
import Lemma.Algebra.EqNegNeg
open Algebra


@[main]
private lemma main
  [InvolutiveNeg α]
  {a b : α}
-- given
  (h : a = -b) :
-- imply
  -a = b := by
-- proof
  apply Eq.of.EqNegS
  rw [EqNegNeg]
  assumption


-- created on 2025-03-29
