import sympy.concrete.quantifier
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.All_Imp.is.All |
| comm | Bool.All.is.All_Imp |
| mp | Bool.All.of.All_Imp |
| mpr | Bool.All_Imp.of.All |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (p q : α → Prop) :
-- imply
  (∀ x, p x → q x) ↔ ∀ x | p x, q x :=
-- proof
  Iff.rfl


-- created on 2018-09-18
-- updated on 2026-08-28
