import Lemma.Algebra.Eq_Neg.of.EqNeg
import Lemma.Bool.BFn_Ite.is.OrAndS
import Lemma.Algebra.EqNeg.of.Eq_Neg
open Algebra Bool


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
