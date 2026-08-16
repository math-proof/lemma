import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.Pow_Add.eq.MulPowS.of.Gt_0 |
| comm | Real.MulPowS.eq.Pow_Add.of.Gt_0 |
-/
@[main, comm]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0)
  (a b : ℝ) :
-- imply
  x ^ (a + b) = x ^ a * x ^ b :=
-- proof
  Real.rpow_add h a b


-- created on 2026-08-16
