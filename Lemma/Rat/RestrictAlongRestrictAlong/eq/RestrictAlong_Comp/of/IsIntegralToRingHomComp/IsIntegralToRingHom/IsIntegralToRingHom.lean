import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
open IsDedekindDomain AlgebraicCurve


/-- ported from external source -/
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
