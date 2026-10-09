import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.Lt_Max.is.Or.Lt |
| mp | Nat.Or.Lt.of.Lt_Max |
| mpr | Nat.Lt_Max.of.Or.Lt |
-/
@[path, mp, mpr]
private lemma main
  [LinearOrder α]
  {x y z : α} :
-- imply
  x < max y z ↔ x < y ∨ x < z :=
-- proof
  lt_max_iff


-- created on 2026-10-07
