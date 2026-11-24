import Lemma.Bool.Or_Not
import Lemma.Bool.Cond.of.Imp.ImpNot.domain_defined.given
open Bool


@[path]
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
-- updated on 2026-09-27
