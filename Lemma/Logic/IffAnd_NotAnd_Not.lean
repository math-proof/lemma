import Lemma.Bool.And_NotAnd_Not.is.OrAndS
open Bool


@[main]
private lemma main
  {p q : Prop} :
-- imply
  p ∧ ¬(q ∧ ¬p) ↔ p := by
-- proof
  rw [And_NotAnd_Not.is.OrAndS]
  tauto


-- created on 2025-04-09
