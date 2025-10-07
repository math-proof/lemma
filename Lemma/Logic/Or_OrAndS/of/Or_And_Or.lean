import Lemma.Bool.And_Or.is.OrAndS
open Bool


@[main]
private lemma main
-- given
  (h : t ∨ p ∧ (q ∨ r)) :
-- imply
  t ∨ p ∧ q ∨ p ∧ r := by
-- proof
  simpa [OrAndS.is.And_Or]


-- created on 2025-04-21
