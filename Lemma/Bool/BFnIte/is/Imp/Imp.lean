import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.BFnIte.is.Imp.Imp |
| comm | Bool.Imp.Imp.is.BFnIte |
| mp | Bool.Imp.Imp.of.BFnIte |
| mpr | Bool.BFnIte.of.Imp.Imp |
-/
@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  {R : β → α → Prop}
  {x : α}
  {a b : β} :
-- imply
  R (if p then
    a
  else
    b) x ↔ (p → R a x) ∧ (¬p → R b x) := by
-- proof
  grind


-- created on 2025-08-12
-- updated on 2026-07-27
