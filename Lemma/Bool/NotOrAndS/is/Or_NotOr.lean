import sympy.Basic


@[main, comm]
private lemma main
-- given
  (p q : Prop) :
-- imply
  ¬((¬p ∧ q) ∨ (p ∧ ¬q)) ↔ (p ∧ q) ∨ ¬(p ∨ q) := by
-- proof
  grind


-- created on 2026-07-26
