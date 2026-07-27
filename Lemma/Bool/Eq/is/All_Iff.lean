import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Eq.is.All_Iff |
| comm | Bool.All_Iff.is.Eq |
| mp | Bool.All_Iff.of.Eq |
| mpr | Bool.Eq.of.All_Iff |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (f g : α → Prop) :
-- imply
  f = g ↔ ∀ x, f x ↔ g x := by
-- proof
  grind


-- created on 2025-07-16
