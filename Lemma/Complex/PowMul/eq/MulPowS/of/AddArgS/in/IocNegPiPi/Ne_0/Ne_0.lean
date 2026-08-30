import sympy.sets.sets
import Lemma.Complex.LogMul.eq.AddLogS.of.AddArgS.in.IocPiS.Ne_0.Ne_0
open Complex


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.PowMul.eq.MulPowS.of.AddArgS.in.IocNegPiPi.Ne_0.Ne_0 |
| comm | Complex.MulPowS.eq.PowMul.of.AddArgS.in.IocNegPiPi.Ne_0.Ne_0 |
-/
@[main, comm]
private lemma main
  {x y : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (h : x.arg + y.arg ∈ Ioc (-π) π)
  (w : ℂ) :
-- imply
  (x * y) ^ w = x ^ w * y ^ w := by
-- proof
  rw [cpow_def_of_ne_zero (mul_ne_zero hx hy), cpow_def_of_ne_zero hx,
    cpow_def_of_ne_zero hy]
  rw [LogMul.eq.AddLogS.of.AddArgS.in.IocPiS.Ne_0.Ne_0 hx hy h]
  rw [add_mul, exp_add]


-- created on 2026-08-28
