import Mathlib.Analysis.SpecialFunctions.Exp
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.Le.is.Le.Exp |
| mp | Real.Le.Exp.of.Le |
| mpr | Real.Le.of.Le.Exp |
-/
@[main, mp, mpr]
private lemma main
  {x y : ℝ} :
-- imply
  x ≤ y ↔ Real.exp x ≤ Real.exp y :=
-- proof
  Real.exp_le_exp.symm


-- created on 2026-10-07
