import Macro.Logic.Quantifier.Part4
import sympy.Basic


@[path]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∃ x | p x, q x) :
-- imply
  ∃ x, p x ∧ q x := by
-- proof
  assumption


-- created on 2018-02-16
