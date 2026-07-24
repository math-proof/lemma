import Lemma.Int.Neg.is.Eq
import Lemma.Int.EqNegNeg
open Int


@[main]
private lemma main
  [InvolutiveNeg α]
  {a b : α}
-- given
  (h : -a = b) :
-- imply
  a = -b := by
-- proof
  apply Eq.of.Neg
  rwa [EqNegNeg]


-- created on 2025-03-29
