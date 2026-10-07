import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Le_Min.is.And.Le |
| mpr | Nat.Le_Min.of.And.Le |
-/
@[main, mpr]
private lemma main
  [LinearOrder α]
  {x y z : α} :
-- imply
  x ≤ min y z ↔ x ≤ y ∧ x ≤ z :=
-- proof
  le_min_iff


-- created on 2022-01-01
-- updated on 2026-10-07
