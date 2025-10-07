import Lemma.Bool.Or_And.is.AndOrS
open Bool


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : r ∨ (p ∧ q)) :
-- imply
  (r ∨ p) ∧ (r ∨ q) := by
-- proof
  rwa [AndOrS.is.Or_And]


-- created on 2025-07-19
