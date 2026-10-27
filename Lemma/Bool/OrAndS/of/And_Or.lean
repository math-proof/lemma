import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p q r : Prop}
-- given
  (h : (p ∨ q) ∧ r) :
-- imply
  (p ∧ r) ∨ (q ∧ r) := by
-- proof
  grind


-- created on 2020-02-18
