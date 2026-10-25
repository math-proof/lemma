import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.Correspondence
import Lemma.Int.P2MUtil

open AlgebraicCurve

/--
[AlgebraicCurve_separableAlong_of_charZero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_separableAlong_of_charZero.lean)
-/
@[path]
private lemma main
  {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁] [CharZero F]
  {φ : F →ₐ[K] F₁}
-- given
  (hφ : φ.toRingHom.IsIntegral) :
-- imply
  SeparableAlong K φ := by
-- proof
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact Algebra.IsSeparable.of_integral F F₁


-- created on 2026-10-23
