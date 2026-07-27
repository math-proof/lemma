import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.NotOrAndS.is.Or_NotOr |
| comm | Bool.Or_NotOr.is.NotOrAndS |
-/
@[main, comm]
private lemma main
-- given
  (p q : Prop) :
-- imply
  ¬((¬p ∧ q) ∨ (p ∧ ¬q)) ↔ (p ∧ q) ∨ ¬(p ∨ q) := by
-- proof
  grind


-- created on 2026-07-26
