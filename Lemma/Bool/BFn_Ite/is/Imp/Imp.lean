import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.BFn_Ite.is.Imp.Imp |
| comm | Bool.Imp.Imp.is.BFn_Ite |
| mp | Bool.Imp.Imp.of.BFn_Ite |
| mpr | Bool.BFn_Ite.of.Imp.Imp |
-/
@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {x : α}
  {a b : β} :
-- imply
  R x (if p then
    a
  else
    b) ↔ (p → R x a) ∧ (¬p → R x b) := by
-- proof
  grind


-- created on 2025-01-12
-- updated on 2026-07-27
