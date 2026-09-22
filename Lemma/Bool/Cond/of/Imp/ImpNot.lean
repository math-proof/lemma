import Lemma.Bool.Or_Not
open Bool


@[main]
private lemma main
  {p q : Prop}
-- given
  (h₀ : p → q)
  (h₁ : ¬p → q) :
-- imply
  q := by
-- proof
  grind


-- created on 2018-05-07
