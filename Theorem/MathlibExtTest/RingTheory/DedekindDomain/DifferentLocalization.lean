/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/DifferentLocalization.lean -/


import Instance.RingTheory.DedekindDomain.DifferentLocalization
import Lemma.Int.DedekindDomain.DifferentLocalization
import Notation.MathlibExtTest.RingTheory.DedekindDomain.DifferentLocalization
set_option autoImplicit false

universe u

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K]
  [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L]
  [IsFractionRing B L]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]

variable (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)

local notation "Aₛ" => Localization.subalgebra.ofField K S hS

variable (SB : Type*) [CommRing SB] [Algebra B SB]
  [IsLocalization (Algebra.algebraMapSubmonoid B S) SB]
  [Algebra (Localization.subalgebra.ofField K S hS) SB] [Algebra SB L] [Algebra A SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB]
  [IsScalarTower A B SB] [IsScalarTower B SB L]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) K L]
  [IsFractionRing SB L] [IsDedekindDomain SB]
  [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB]
  [Module.IsTorsionFree B SB]
  [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]

/-!
# Tests for different ideals under canonical localization (ATLAS N241)

Generic application examples exercising
`FractionalIdeal.extendedHom_dual_one_eq_dual_one_ofField` and
`Ideal.map_differentIdeal_eq_localization_ofField`, plus a membership-facing
consequence of the fractional equality. These are API/inference tests; no new
definitions are introduced.
-/


/-- Generic application of the fractional trace-dual localization equality. -/
example :
    FractionalIdeal.extendedHom L SB
        (FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) =
      FractionalIdeal.dual Aₛ K (1 : FractionalIdeal (nonZeroDivisors SB) L) :=
  FractionalIdeal.extendedHom_dual_one_eq_dual_one_ofField A K L B S hS SB

/-- Generic application of the different-ideal localization equality. -/
-- The universe level of `L` is captured through the proof term, which names `L`
-- when applying the theorem; the section already supplies `[IsFractionRing B L]`,
-- so no additional binder is introduced here.
example :
    Ideal.map (algebraMap B SB) (differentIdeal A B) = differentIdeal Aₛ SB :=
  Ideal.map_differentIdeal_eq_localization_ofField A K L B S hS SB

/-- Membership-facing consequence of the fractional equality. -/
example (x : L) :
    x ∈ FractionalIdeal.extendedHom L SB
        (FractionalIdeal.dual A K (1 : FractionalIdeal (nonZeroDivisors B) L)) ↔
      x ∈ FractionalIdeal.dual Aₛ K (1 : FractionalIdeal (nonZeroDivisors SB) L) := by
  rw [FractionalIdeal.extendedHom_dual_one_eq_dual_one_ofField A K L B S hS SB]

