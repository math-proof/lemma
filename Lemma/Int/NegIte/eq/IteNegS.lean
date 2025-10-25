import Lemma.Int.Eq_Neg.of.EqNeg
import Lemma.Bool.BFn_Ite.is.OrAndS
import Lemma.Int.EqNeg.of.Eq_Neg
open Bool Int


@[main]
private lemma main
  [Decidable p]
  [Neg α]
-- given
  (a b : α) :
-- imply
  (if p then
    -a
  else
    -b) = -if p then
    a
  else
    b := by
-- proof
  split_ifs with h <;> rfl


-- created on 2025-04-26
-- updated on 2025-05-14
