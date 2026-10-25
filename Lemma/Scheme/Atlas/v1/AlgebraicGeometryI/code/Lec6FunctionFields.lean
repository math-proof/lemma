import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec6FunctionFields
open CategoryTheory Opposite Lec6
open AlgebraicGeometry TopologicalSpace


namespace Lec6

/--
[functionField_germ_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma functionField_germ_injective
  {X : AlgebraicGeometry.Scheme}
  [IsIntegral X]
  {U : X.Opens}
  [Nonempty U] :
-- imply
  Function.Injective (X.germToFunctionField U) :=
-- proof
  AlgebraicGeometry.Scheme.germToFunctionField_injective X U

end Lec6

namespace Lec6

/--
[functionField_isFractionRing_of_affineOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma functionField_isFractionRing_of_affineOpen
  {X : AlgebraicGeometry.Scheme}
  [IsIntegral X]
  {U : X.Opens}
  [Nonempty U]
-- given
  (hU : IsAffineOpen U) :
-- imply
  IsFractionRing Γ(X, U) X.functionField :=
-- proof
  AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X U hU

end Lec6

namespace Lec6

/--
[ramificationLocus_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma ramificationLocus_isClosed
  {A B : Type*}
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B] :
-- imply
  IsClosed (RamificationLocus A B) :=
-- proof
  PrimeSpectrum.isClosed_zeroLocus _

end Lec6

namespace Lec6

/--
[ramificationLocus_ne_univ_of_discr_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma ramificationLocus_ne_univ_of_discr_ne_zero
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B]
-- given
  (hd : Algebra.discr A (Module.Free.chooseBasis A B) ≠ 0) :
-- imply
  RamificationLocus A B ≠ Set.univ := by
-- proof
  intro h
  have hmem := (PrimeSpectrum.zeroLocus_eq_univ_iff _).mp h
  simp only [Set.singleton_subset_iff, SetLike.mem_coe] at hmem
  rw [nilradical_eq_zero] at hmem
  exact hd hmem

end Lec6

namespace Lec6

/--
[discr_ne_zero_of_separable_functionField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma discr_ne_zero_of_separable_functionField
  {A : Type*}
  {K : Type*}
  {B : Type*}
  {L : Type*}
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [CommRing B]
  [IsDomain B]
  [Field L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [IsScalarTower A B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
  [Algebra.IsSeparable K L]
  [Module.Finite K L] :
-- imply
  Algebra.discr A (Module.Free.chooseBasis A B) ≠ 0 := by
-- proof
  set b := Module.Free.chooseBasis A B
  set b' := b.localizationLocalization K (nonZeroDivisors A) L
  have hlocal : Algebra.discr K b' = (algebraMap A K) (Algebra.discr A b) :=
    Algebra.discr_localizationLocalization A (nonZeroDivisors A) L b
  have hne : Algebra.discr K b' ≠ 0 := Algebra.discr_not_zero_of_basis K b'
  rw [hlocal] at hne
  exact fun h => hne (by rw [h, map_zero])

end Lec6

namespace Lec6

/--
[ramificationLocus_ne_univ_of_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma ramificationLocus_ne_univ_of_separable
  {A : Type*}
  {K : Type*}
  {B : Type*}
  {L : Type*}
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [CommRing B]
  [IsDomain B]
  [Field L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [IsScalarTower A B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
  [Algebra.IsSeparable K L]
  [Module.Finite K L] :
-- imply
  RamificationLocus A B ≠ Set.univ :=
-- proof
  ramificationLocus_ne_univ_of_discr_ne_zero A B
    (discr_ne_zero_of_separable_functionField A K B L)

end Lec6

namespace Lec6

/--
[ramificationLocus_properClosed_of_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma ramificationLocus_properClosed_of_separable
  {A : Type*}
  {K : Type*}
  {B : Type*}
  {L : Type*}
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [CommRing B]
  [IsDomain B]
  [Field L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A B]
  [Module.Finite A B]
  [Module.Free A B]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [IsScalarTower A B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
  [Algebra.IsSeparable K L]
  [Module.Finite K L] :
-- imply
  IsClosed (RamificationLocus A B) ∧ RamificationLocus A B ≠ Set.univ :=
-- proof
  ⟨ramificationLocus_isClosed A B, ramificationLocus_ne_univ_of_separable A K B L⟩

end Lec6

namespace Lec6

/--
[normalization_is_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma normalization_is_normal
  [CommRing R]
  [IsDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  [Field L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R K L]
  [FiniteDimensional K L] :
-- imply
  IsIntegrallyClosed (integralClosure R L) :=
-- proof
  integralClosure.isIntegrallyClosedOfFiniteExtension K

end Lec6

namespace Lec6

/--
[normalization_map_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma normalization_map_injective
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  {K : Type*}
  [Field K]
  [Algebra B K]
  [IsFractionRing B K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra B L]
  [IsScalarTower B K L] :
-- imply
  Function.Injective (algebraMap B (integralClosure B L)) := by
-- proof
  haveI : IsScalarTower B (integralClosure B L) L :=
    IsScalarTower.subalgebra' B L L (integralClosure B L)
  exact algebraMap_injective_of_field_isFractionRing B (↥(integralClosure B L)) K L

end Lec6

namespace Lec6

/--
[normalization_finite_module](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma normalization_finite_module
  [CommRing B]
  [IsDomain B]
  [IsIntegrallyClosed B]
  [IsNoetherianRing B]
  {K : Type*}
  [Field K]
  [Algebra B K]
  [IsFractionRing B K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra B L]
  [IsScalarTower B K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L] :
-- imply
  Module.Finite B (integralClosure B L) :=
-- proof
  IsIntegralClosure.finite B K L (integralClosure B L)

end Lec6

namespace Lec6

/--
[integral_closure_noetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma integral_closure_noetherian
  [CommRing R]
  [IsDomain R]
  [IsIntegrallyClosed R]
  [IsNoetherianRing R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L] :
-- imply
  IsNoetherianRing (integralClosure R L) :=
-- proof
  integralClosure.isNoetherianRing (K := K) L

end Lec6

namespace Lec6

/--
[normalization_finiteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma normalization_finiteType
  {k : Type*}
  [Field k]
  [CommRing B]
  [IsDomain B]
  [Algebra k B]
  [Algebra.FiniteType k B]
  [IsIntegrallyClosed B]
  [IsNoetherianRing B]
  {K : Type*}
  [Field K]
  [Algebra B K]
  [IsFractionRing B K]
  [Algebra k K]
  [IsScalarTower k B K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra B L]
  [IsScalarTower B K L]
  [Algebra k L]
  [IsScalarTower k B L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L] :
-- imply
  Algebra.FiniteType k (integralClosure B L) := by
-- proof
  haveI : Module.Finite B (integralClosure B L) :=
    normalization_finite_module K L
  exact Algebra.FiniteType.trans (‹Algebra.FiniteType k B›)
    (Module.Finite.finiteType (integralClosure B L))

end Lec6

namespace Lec6

/--
[yoneda_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma yoneda_full
  {C : Type*}
  [Category C] :
-- imply
  (coyoneda (C := C)).Full :=
-- proof
  (yoneda_fully_faithful C).full

end Lec6

namespace Lec6

/--
[yoneda_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma yoneda_faithful
  {C : Type*}
  [Category C] :
-- imply
  (coyoneda (C := C)).Faithful :=
-- proof
  (yoneda_fully_faithful C).faithful

end Lec6

namespace Lec6

/--
[isNormalVariety_of_integrallyClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma isNormalVariety_of_integrallyClosed
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsIntegrallyClosed R] :
-- imply
  IsNormalVariety R :=
-- proof
  ‹IsIntegrallyClosed R›

end Lec6

namespace Lec6

/--
[normalization_isNormalVariety](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma normalization_isNormalVariety
  [CommRing R]
  [IsDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  [Field L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R K L]
  [FiniteDimensional K L] :
-- imply
  IsNormalVariety (integralClosure R L) :=
-- proof
  normalization_is_normal K

end Lec6

namespace Lec6

/--
[dedekindDomain_localRing_isRegularLocalRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma dedekindDomain_localRing_isRegularLocalRing
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  [IsLocalRing R]
-- given
  (h : ¬ IsField R) :
-- imply
  IsRegularLocalRing R := by
-- proof
  have : IsDiscreteValuationRing R := by
    have tfae := IsDiscreteValuationRing.TFAE R h
    exact (tfae.out 2 0).mp ‹IsDedekindDomain R›
  exact IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing R

end Lec6

namespace Lec6

/--
[dedekindDomain_isIntegrallyClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma dedekindDomain_isIntegrallyClosed
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R] :
-- imply
  IsIntegrallyClosed R :=
-- proof
  inferInstance

end Lec6

namespace Lec6

/--
[dedekindDomain_isNormalVariety](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean)
-/
@[path]
lemma dedekindDomain_isNormalVariety
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R] :
-- imply
  IsNormalVariety R :=
-- proof
  dedekindDomain_isIntegrallyClosed R
end Lec6



-- created on 2026-10-23
