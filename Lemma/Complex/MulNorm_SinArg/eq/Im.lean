import Notation.Analysis.Complex.Complexes
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Complex.MulNorm_SinArg.eq.Im |
| comm | Complex.Im.eq.MulNorm_SinArg |
-/
@[path, comm]
private lemma main
  {z : ℂ} :
-- imply
  ‖z‖ * Real.sin (arg z) = im z :=
-- proof
  Complex.norm_mul_sin_arg z


-- created on 2018-07-25
-- updated on 2026-10-26
