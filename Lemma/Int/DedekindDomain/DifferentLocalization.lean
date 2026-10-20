import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.DifferentLocalization
open FractionalIdeal


/--
[extendedHom_dual_one_eq_dual_one_ofField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentLocalization.lean)
-/
@[path]
private lemma extendedHom_dual_one_eq_dual_one_ofField_eq
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B] [IsFractionRing A K] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [CommRing SB] [Algebra B SB] [Algebra A SB] [IsScalarTower A B SB] [IsDedekindDomain SB] [Module.IsTorsionFree B SB]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [IsFractionRing B L] [Algebra SB L] [IsScalarTower B SB L] [IsFractionRing SB L]
  {S : Submonoid A} [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) L] [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L] [IsScalarTower (Localization.subalgebra.ofField K S hS) K L] [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB] [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]
-- given
  (hS : S ≤ nonZeroDivisors A) :
-- imply
  extendedHom L SB (dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) =
    dual Aₛ K (1 : FractionalIdeal (nonZeroDivisors SB) L) := by
-- proof
  apply FractionalIdeal.extendedHom_dual_one_eq_dual_one_ofField A K L B S hS SB

/--
[Ideal.map_differentIdeal_eq_localization_ofField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentLocalization.lean)
-/
@[path]
private lemma Ideal_map_differentIdeal_eq_localization_ofField_eq
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B] [IsFractionRing A K] [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [CommRing SB] [Algebra B SB] [Algebra A SB] [IsScalarTower A B SB] [IsDedekindDomain SB] [Module.IsTorsionFree B SB]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [Algebra SB L] [IsScalarTower B SB L] [IsFractionRing SB L] [IsFractionRing B L]
  {S : Submonoid A} [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB] [IsScalarTower A (Localization.subalgebra.ofField K S hS) L] [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L] [IsScalarTower (Localization.subalgebra.ofField K S hS) K L] [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB] [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]
-- given
  (hS : S ≤ nonZeroDivisors A) :
-- imply
  Ideal.map (algebraMap B SB) (differentIdeal A B) = differentIdeal Aₛ SB := by
-- proof
  apply Ideal.map_differentIdeal_eq_localization_ofField A K L B S hS SB


-- created on 2026-10-20
