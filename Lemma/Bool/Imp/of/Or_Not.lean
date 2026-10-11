import Lemma.Bool.Imp.is.OrNot
import sympy.Basic
open Bool


@[path]
private lemma main
  {p q : Prop}
-- given
  (h : p → q) :
-- imply
  ¬ p ∨ q := by
-- proof
  exact OrNot.of.Imp h


-- created on 2018-01-31
