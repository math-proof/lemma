import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.NormalizationVariety
open NormalizationVariety


namespace NormalizationVariety

/--
[normalization_is_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalizationVariety.lean)
-/
@[path]
lemma normalization_is_finite
  {k A : Type*}
  [Field k]
  [CommRing A]
  [IsDomain A]
  [Algebra k A]
  [Algebra.FiniteType k A]
  [IsIntegrallyClosed A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {E : Type*}
  [Field E]
  [Algebra K E]
  [FiniteDimensional K E]
  [Algebra A E]
  [IsScalarTower A K E]
  [Algebra.IsSeparable K E] :
-- imply
  Module.Finite A (integralClosure A E) := by
-- proof
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsScalarTower A (↥(integralClosure A E)) E :=
    IsScalarTower.subalgebra' A E E (integralClosure A E)
  exact IsIntegralClosure.finite A K E (integralClosure A E)

end NormalizationVariety

namespace NormalizationVariety

/--
[normalization_finiteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalizationVariety.lean)
-/
@[path]
lemma normalization_finiteType
  {k A : Type*}
  [Field k]
  [CommRing A]
  [IsDomain A]
  [Algebra k A]
  [Algebra.FiniteType k A]
  [IsIntegrallyClosed A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Algebra k K]
  [IsScalarTower k A K]
  {E : Type*}
  [Field E]
  [Algebra K E]
  [FiniteDimensional K E]
  [Algebra A E]
  [IsScalarTower A K E]
  [Algebra k E]
  [IsScalarTower k A E]
  [Algebra.IsSeparable K E] :
-- imply
  Algebra.FiniteType k (integralClosure A E) := by
-- proof
  haveI : Module.Finite A (integralClosure A E) :=
    normalization_is_finite k A K E
  exact Algebra.FiniteType.trans (‹Algebra.FiniteType k A›)
    (Module.Finite.finiteType (integralClosure A E))

end NormalizationVariety

namespace NormalizationVariety

/--
[normalization_is_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalizationVariety.lean)
-/
@[path]
lemma normalization_is_normal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {E : Type*}
  [Field E]
  [Algebra K E]
  [FiniteDimensional K E]
  [Algebra A E]
  [IsScalarTower A K E] :
-- imply
  IsIntegrallyClosed (integralClosure A E) :=
-- proof
  integralClosure.isIntegrallyClosedOfFiniteExtension K

end NormalizationVariety

namespace NormalizationVariety

/--
[normalization_map_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalizationVariety.lean)
-/
@[path]
lemma normalization_map_injective
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {E : Type*}
  [Field E]
  [Algebra K E]
  [Algebra A E]
  [IsScalarTower A K E] :
-- imply
  Function.Injective (algebraMap A (integralClosure A E)) := by
-- proof
  haveI : IsScalarTower A (integralClosure A E) E :=
    IsScalarTower.subalgebra' A E E (integralClosure A E)
  exact algebraMap_injective_of_field_isFractionRing A (↥(integralClosure A E)) K E

end NormalizationVariety

namespace NormalizationVariety

/--
[normalization_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalizationVariety.lean)
-/
@[path]
lemma normalization_existence
  {k A : Type*}
  [Field k]
  [CommRing A]
  [IsDomain A]
  [Algebra k A]
  [Algebra.FiniteType k A]
  [IsIntegrallyClosed A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Algebra k K]
  [IsScalarTower k A K]
  {E : Type*}
  [Field E]
  [Algebra K E]
  [FiniteDimensional K E]
  [Algebra A E]
  [IsScalarTower A K E]
  [Algebra k E]
  [IsScalarTower k A E]
  [Algebra.IsSeparable K E] :
-- imply
  Module.Finite A (integralClosure A E) ∧ Algebra.FiniteType k (integralClosure A E) ∧ IsIntegrallyClosed (integralClosure A E) ∧ Function.Injective (algebraMap A (integralClosure A E)) := by
-- proof
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact normalization_is_finite k A K E
  · exact normalization_finiteType k A K E
  · exact normalization_is_normal A K E
  · exact normalization_map_injective A K E

end NormalizationVariety

namespace NormalizationVariety

/--
[normalization_factorization_scheme](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalizationVariety.lean)
-/
@[path]
lemma normalization_factorization_scheme
  {X Y : Scheme}
  {f : X ⟶ Y}
  [QuasiCompact f]
  [QuasiSeparated f] :
-- imply
  f.toNormalization ≫ f.fromNormalization = f :=
-- proof
  f.toNormalization_fromNormalization

end NormalizationVariety

namespace NormalizationVariety

/--
[normalization_fromNormalization_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalizationVariety.lean)
-/
@[path]
lemma normalization_fromNormalization_integral
  {X Y : Scheme}
  {f : X ⟶ Y}
  [QuasiCompact f]
  [QuasiSeparated f] :
-- imply
  IsIntegralHom f.fromNormalization :=
-- proof
  inferInstance

end NormalizationVariety

namespace NormalizationVariety

/--
[normalization_toNormalization_dominant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalizationVariety.lean)
-/
@[path]
lemma normalization_toNormalization_dominant
  {X Y : Scheme}
  {f : X ⟶ Y}
  [QuasiCompact f]
  [QuasiSeparated f] :
-- imply
  IsDominant f.toNormalization :=
-- proof
  inferInstance

end NormalizationVariety

namespace NormalizationVariety

/--
[normalization_sections_isIntegralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalizationVariety.lean)
-/
@[path]
lemma normalization_sections_isIntegralClosure
  {X Y : Scheme}
  {f : X ⟶ Y}
  [QuasiCompact f]
  [QuasiSeparated f]
  {U : Y.Opens}
-- given
  (hU : IsAffineOpen U) :
-- imply
  letI := (f.app U).hom.toAlgebra Nonempty (Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅ CommRingCat.of (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) :=
-- proof
  ⟨f.normalizationObjIso hU⟩
end NormalizationVariety



-- created on 2026-10-23
