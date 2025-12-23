import Lemma.Rat.Div_Neg.eq.NegDiv
import Lemma.Int.EqNegNeg
import Lemma.Rat.DivNeg.eq.NegDiv
open Int Rat


@[main]
private lemma main
  [DivisionMonoid α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -a / -b = a / b := by
-- proof
  rw [DivNeg.eq.NegDiv]
  rw [Div_Neg.eq.NegDiv]
  rw [EqNegNeg]


-- created on 2025-12-23
