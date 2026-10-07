import Mathlib
import sympy.Basic


/--
[IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization.lean)
-/

private lemma  IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization
    {C : Type*} [CommRing C] [IsDomain C] (M : Submonoid C) (hM : M ≤ nonZeroDivisors C)
    (L : Type*) [CommRing L] [IsDomain L] [Algebra C L] [IsLocalization M L]
    [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L] : IsIntegrallyClosed C := by
  let K := FractionRing C
  have hg : ∀ y : M, IsUnit (algebraMap C K y) := fun y =>
    isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective C K)).mpr (nonZeroDivisors.ne_zero (hM y.2)))
  let algLK : Algebra L K := (IsLocalization.lift (M := M) (S := L) hg).toAlgebra
  have : IsScalarTower C L K :=
    IsScalarTower.of_algebraMap_eq' (R := C) (S := L) (A := K) (IsLocalization.lift_comp (M := M) hg).symm
  have : IsFractionRing L K := IsFractionRing.isFractionRing_of_isLocalization M L K hM
  refine (isIntegrallyClosed_iff K).mpr fun {x} hx => ?_
  have hxL : IsIntegral L x := hx.tower_top
  obtain ⟨l, rfl⟩ := (isIntegrallyClosed_iff K).mp inferInstance hxL
  have hl : IsIntegral C l :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom C L K) (IsFractionRing.injective L K)).mp hx
  obtain ⟨c, rfl⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hl
  exact ⟨c, IsScalarTower.algebraMap_apply C L K c⟩
@[main]
private lemma main
  [CommRing C] [IsDomain C] [CommRing L] [IsDomain L] [Algebra C L] [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L]
  {M : Submonoid C} [IsLocalization M L]
-- given
  (hM : M ≤ nonZeroDivisors C) :
-- imply
  IsIntegrallyClosed C :=
-- proof
  IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization M hM L


-- created on 2026-10-05
