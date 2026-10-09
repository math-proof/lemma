import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.NotOr.is.Imp.Not |
| comm | Bool.Imp.Not.is.NotOr |
-/
@[path, comm]
private lemma main
-- given
  (p q : Prop) :
-- imply
  ¬(p ∨ q) ↔ (q → p) ∧ ¬p := by
-- proof
  grind


-- created on 2025-04-09
-- updated on 2026-07-26
