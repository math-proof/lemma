import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Int.Lt_Abs.is.And |
| mp | Int.And.of.Lt_Abs |
| mpr | Int.Lt_Abs.of.And |
-/
@[path, mp, mpr]
private lemma main
  {x a : ℤ} :
-- imply
  |x| < a ↔ x < a ∧ x > -a :=
-- proof
  abs_lt.trans And.comm


-- created on 2026-10-07
