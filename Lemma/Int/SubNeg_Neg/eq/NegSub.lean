import Lemma.Int.Sub.eq.NegSub
import Lemma.Int.SubNeg_Neg.eq.Sub
open Int


@[main, comm]
private lemma main
  [AddCommGroup α]
-- given
  (a b : α) :
-- imply
  -a - -b = -(a - b) := by
-- proof
  rw [SubNeg_Neg.eq.Sub]
  rw [NegSub.eq.Sub]


-- created on 2026-07-08
