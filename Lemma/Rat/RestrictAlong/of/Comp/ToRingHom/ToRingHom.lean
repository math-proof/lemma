import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.Correspondence
import Lemma.Int.P2MUtil

open IsDedekindDomain AlgebraicCurve

/--
[AlgebraicCurve_Place_restrictAlong_restrictAlong](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_restrictAlong_restrictAlong.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F'']
  {φ : F →ₐ[K] F'}
  {χ : F' →ₐ[K] F''}
  {W : Place K F''}
-- given
  (hφ : φ.toRingHom.IsIntegral)
  (hχ : χ.toRingHom.IsIntegral)
  (hχφ : (χ.comp φ).toRingHom.IsIntegral) :
-- imply
  (W.restrictAlong χ hχ).restrictAlong φ hφ = W.restrictAlong (χ.comp φ) hχφ :=
-- proof
  Place.ext (SetLike.ext fun _ => Iff.rfl)


-- created on 2026-10-23
