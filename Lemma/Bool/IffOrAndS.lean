import Lemma.Bool.And_Or.is.OrAndS
import Lemma.Bool.Or_Not
open Bool


@[main]
private lemma main
  {p q : Prop} :
-- imply
  p ∧ q ∨ p ∧ ¬q ↔ p := by
-- proof
  simp [OrAndS.is.And_Or]
  simp [Or_Not]


-- created on 2025-04-09
-- updated on 2025-04-21
