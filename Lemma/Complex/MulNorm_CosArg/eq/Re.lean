import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.MulNorm_CosArg.eq.Re |
| comm | Complex.Re.eq.MulNorm_CosArg |
-/
@[main, comm]
private lemma main
  {z : ℂ} :
-- imply
  ‖z‖ * Real.cos (arg z) = re z :=
-- proof
  Complex.norm_mul_cos_arg z


-- created on 2018-06-13
-- updated on 2026-08-30
