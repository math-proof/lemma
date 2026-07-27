import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.BFn_Ite.is.OrAndS |
| comm | Bool.OrAndS.is.BFn_Ite |
| mp | Bool.OrAndS.of.BFn_Ite |
| mpr | Bool.BFn_Ite.of.OrAndS |
-/
@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
-- given
  (R : α → β → Prop)
  (x : α)
  (a b : β) :
-- imply
  R x (if p then
    a
  else
    b) ↔ R x a ∧ p ∨ R x b ∧ ¬p := by
-- proof
  grind


-- created on 2025-01-12
-- updated on 2026-07-27
