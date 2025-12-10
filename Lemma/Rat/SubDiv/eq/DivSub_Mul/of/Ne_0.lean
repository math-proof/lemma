import Lemma.Int.EqNegS.is.Eq
import Lemma.Int.Sub.eq.NegSub
import Lemma.Rat.DivNeg.eq.NegDiv
import Lemma.Rat.Sub_Div.eq.DivSubMul.of.Ne_0
open Int Rat


@[main, comm]
private lemma main
  [DivisionRing α]
  {b : α}
-- given
  (h : b ≠ 0)
  (x a : α) :
-- imply
  a / b - x = (a - x * b) / b := by
-- proof
  apply Eq.of.EqNegS
  rw [NegDiv.eq.DivNeg]
  repeat rw [NegSub.eq.Sub]
  apply Sub_Div.eq.DivSubMul.of.Ne_0 h


-- created on 2025-12-10
