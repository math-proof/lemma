/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/FractionalIdeal/Extended.lean -/


import Lemma.Int.FractionalIdeal.Extended
import Mathlib.Tactic.NormNum


namespace MathlibExtTest

open nonZeroDivisors FractionalIdeal

section Localized

variable {R S K : Type*} [CommRing R] [CommRing S] [CommRing K]

variable [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

variable {p : Submonoid R} [IsLocalization p S]

variable [IsLocalizedModule p (.id : K →ₗ[R] K)]

example (I J : Submodule R K) (hJ : J.FG) :
    (I / J).localized' S p (.id : K →ₗ[R] K) =
      I.localized' S p (.id : K →ₗ[R] K) / J.localized' S p (.id : K →ₗ[R] K) :=
  Submodule.localized'_div_of_fg I J hJ

end Localized

section Extended

variable {A B K : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]

variable [Field K] [Algebra A B] [Module.IsTorsionFree A B]

variable [Algebra A K] [Algebra B K] [IsScalarTower A B K]

variable [IsFractionRing A K] [IsFractionRing B K]

example (S : Submonoid A) [IsLocalization S B] (I J : FractionalIdeal A⁰ K)
    (hJ0 : J ≠ 0) (hJ : (J : Submodule A K).FG) :
    extendedHom K B (I / J) = extendedHom K B I / extendedHom K B J :=
  extendedHom_div_of_fg S I J hJ0 hJ

example [IsNoetherianRing A] (S : Submonoid A) [IsLocalization S B]
    (I J : FractionalIdeal A⁰ K) (hJ : J ≠ 0) :
    extendedHom K B (I / J) = extendedHom K B I / extendedHom K B J :=
  extendedHom_div S I J hJ

end Extended

section AtPrime

variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]

variable (P : Ideal A) [P.IsPrime]

example (I J : FractionalIdeal A⁰ (FractionRing A)) (hJ : J ≠ 0) :
    extendedHom (FractionRing A) (Localization.AtPrime P) (I / J) =
      extendedHom (FractionRing A) (Localization.AtPrime P) I /
        extendedHom (FractionRing A) (Localization.AtPrime P) J :=
  extendedHom_div P.primeCompl I J hJ

end AtPrime

section Integer

example (I J : FractionalIdeal ℤ⁰ ℚ) (hJ : J ≠ 0) :
    extendedHom ℚ ℤ (I / J) = extendedHom ℚ ℤ I / extendedHom ℚ ℤ J :=
  extendedHom_div (IsUnit.submonoid ℤ) I J hJ

-- Unit-localization check over ℤ ⊆ ℚ, independent of the new localization/division theorems.
example :
    extendedHom ℚ ℤ
      (FractionalIdeal.spanSingleton ℤ⁰ (6 : ℚ) /
        FractionalIdeal.spanSingleton ℤ⁰ (2 : ℚ)) =
      FractionalIdeal.spanSingleton ℤ⁰ (3 : ℚ) := by
  rw [FractionalIdeal.spanSingleton_div_spanSingleton,
    FractionalIdeal.extendedHom_spanSingleton]
  have hmap :
      (IsFractionRing.map (K := ℚ) (L := ℚ) (j := algebraMap ℤ ℤ)
        (FaithfulSMul.algebraMap_injective ℤ ℤ)) = RingHom.id ℚ :=
    Subsingleton.elim _ _
  rw [hmap, RingHom.id_apply]
  norm_num

end Integer
end MathlibExtTest
