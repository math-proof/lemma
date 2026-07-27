import sympy.concrete.quantifier
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.All.is.All.AllNot |
| mp | Bool.All.AllNot.of.All |
| mpr | Bool.All.of.All.AllNot |
-/
@[main, mp, mpr]
private lemma main
-- given
  (f p : α → Prop) :
-- imply
  (∀ e, f e) ↔ (∀ e | p e, f e) ∧ (∀ e | ¬p e, f e) := by
-- proof
  grind


-- created on 2025-08-04
