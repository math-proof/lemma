import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Real Complex Set
open scoped Topology


/--
[Complex.betaIntegral_eq_Gamma_mul_div_Lecture18](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture18.lean)
-/
@[path]
lemma Complex.betaIntegral_eq_Gamma_mul_div_Lecture18
  {z w : ℂ}
-- given
  (hz : 0 < z.re)
  (hw : 0 < w.re) :
-- imply
  Complex.betaIntegral z w = Complex.Gamma z * Complex.Gamma w / Complex.Gamma (z + w) :=
-- proof
  Complex.betaIntegral_eq_Gamma_mul_div z w hz hw


-- created on 2026-10-23
