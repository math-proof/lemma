import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.MulNorm_SinArg.eq.Im |
| comm | Complex.Im.eq.MulNorm_SinArg |
-/
@[main, comm]
private lemma main
  {z : ℂ} :
-- imply
  ‖z‖ * Real.sin (arg z) = im z :=
-- proof
  Complex.norm_mul_sin_arg z


-- created on 2018-07-25
-- updated on 2026-08-30
