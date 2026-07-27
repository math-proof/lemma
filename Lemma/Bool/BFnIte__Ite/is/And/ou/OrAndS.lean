import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.BFnIte__Ite.is.And.ou.OrAndS |
| comm | Bool.And.ou.OrAndS.is.BFnIte__Ite |
| mp | Bool.And.ou.OrAndS.of.BFnIte__Ite |
| mpr | Bool.BFnIte__Ite.of.And.ou.OrAndS |
-/
@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  [Decidable q]
  {R : α → β → Prop}
  {x : β}
  {a b c : α} :
-- imply
  R (if p then
    a
  else if q then
    b
  else
    c) x ↔ R a x ∧ p ∨ R b x ∧ q ∧ ¬p ∨ R c x ∧ ¬(p ∨ q) := by
-- proof
  grind


-- created on 2025-08-02
-- updated on 2026-07-27
