import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.EqSqrt_0.is.Le_0 |
| comm | Real.Le_0.is.EqSqrt_0 |
| mp | Real.Le_0.of.EqSqrt_0 |
| mpr | Real.EqSqrt_0.of.Le_0 |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ) :
-- imply
  √x = 0 ↔ x ≤ 0 :=
-- proof
  Real.sqrt_eq_zero'


-- created on 2025-01-17
