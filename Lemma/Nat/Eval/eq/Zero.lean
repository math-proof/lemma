import Mathlib
import sympy.Basic
import Lemma.ModularCurve.KroneckerTransport
import Lemma.Int.P2MUtil

open PowerSeries HahnSeries IntermediateField ModularCurve

/--
[ModularCurve_ModularPolynomialData_eval_int_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_ModularPolynomialData_eval_int_eq_zero.lean)
-/
@[path]
private lemma main
  {N : ℕ} [NeZero N]
  {data : ModularCurve.ModularPolynomialData N} :
-- imply
  data.Φ.eval₂ ModularCurve.evalAtJInt (ModularCurve.jqIntN N) = 0 := by
-- proof
  refine laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective ?_
  rw [map_zero, Polynomial.hom_eval₂, laurentMap_comp_evalAtJInt, laurentMap_jqIntN]
  apply data.eval_eq_zero


-- created on 2026-10-23
