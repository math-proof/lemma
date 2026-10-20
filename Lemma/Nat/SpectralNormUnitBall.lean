import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SpectralNormUnitBall
open Polynomial
open MetaMathlibExt


/--
[spectralNorm_le_one_iff_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SpectralNormUnitBall.lean)
-/
@[path]
private lemma spectralNorm_le_one_iff_isIntegral_eq
  [CommRing A] [IsDomain A] [NontriviallyNormedField K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L]
  {x : L}
-- given
  (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y) :
-- imply
  spectralNorm K L x ≤ 1 ↔ IsIntegral A x := by
-- proof
  apply MetaMathlibExt.spectralNorm_le_one_iff_isIntegral hA x

/--
[spectralNorm_le_one_iff_exists_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SpectralNormUnitBall.lean)
-/
@[path]
private lemma spectralNorm_le_one_iff_exists_integralClosure_eq
  [CommRing A] [IsDomain A] [NontriviallyNormedField K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K L] [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  {x : L}
-- given
  (hA : ∀ y : K, ‖y‖ ≤ 1 ↔ IsIntegral A y) :
-- imply
  spectralNorm K L x ≤ 1 ↔ ∃ b : B, algebraMap B L b = x := by
-- proof
  apply MetaMathlibExt.spectralNorm_le_one_iff_exists_integralClosure hA x


-- created on 2026-10-20
