import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Abs.is.OrEqS |
| comm | Int.OrEqS.is.Abs |
| mp | Int.OrEqS.of.Abs |
| mpr | Int.Abs.of.OrEqS |
-/
@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [LinearOrder α]
  {x y : α} :
-- imply
  |y| = |x| ↔ y = x ∨ y = -x :=
-- proof
  abs_eq_abs


-- created on 2018-08-14
-- updated on 2026-08-23
