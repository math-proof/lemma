import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.BFnIte.is.OrAndS |
| comm | Bool.OrAndS.is.BFnIte |
| mp | Bool.OrAndS.of.BFnIte |
| mpr | Bool.BFnIte.of.OrAndS |
-/
@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
-- given
  (R : β → α → Prop)
  (x : α)
  (a b : β) :
-- imply
  R (if p then
    a
  else
    b) x ↔ R a x ∧ p ∨ R b x ∧ ¬p := by
-- proof
  grind


-- created on 2025-04-12
-- updated on 2026-07-27
