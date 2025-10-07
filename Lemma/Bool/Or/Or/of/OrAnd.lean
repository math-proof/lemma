import Lemma.Bool.OrAnd.is.AndOrS
open Bool


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : p ∧ q ∨ r) :
-- imply
  (p ∨ r) ∧ (q ∨ r) := by
-- proof
  rwa [AndOrS.is.OrAnd]


-- created on 2025-07-19
