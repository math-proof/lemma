/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/RamificationInertia/Valuation.lean -/


import Lemma.Int.RamificationInertia.Valuation
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Tests for the valuation bridge

Exercises for `MathlibExt.RingTheory.RamificationInertia.Valuation`:
the `emultiplicity`/`addVal` identification, the scaling of `addVal`
along a torsion-free local DVR extension, and the residue-characteristic
criterion for natural casts, generically and in one concrete 5-adic case.
-/

-- Identification endpoint, generic: a unit has vanishing ideal multiplicity.
example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (x : R) (hx : IsUnit x) :
    emultiplicity (IsLocalRing.maximalIdeal R) (Ideal.span {x}) = 0 := by
  rw [IsDiscreteValuationRing.emultiplicity_maximalIdeal_span_eq_addVal,
    IsDiscreteValuationRing.addVal_eq_zero_iff]
  exact hx

-- Scaling endpoint, generic: scaling preserves vanishing valuations.
example {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    [IsLocalHom (algebraMap A B)] (x : A)
    (hx : IsDiscreteValuationRing.addVal A x = 0) :
    IsDiscreteValuationRing.addVal B (algebraMap A B x) = 0 := by
  rw [IsDiscreteValuationRing.addVal_algebraMap_eq_ramificationIdx_mul, hx,
    mul_zero]

-- Unit criterion endpoint, generic: valuation of a natural cast.
example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (n : ℕ) :
    IsDiscreteValuationRing.addVal R (n : R) = 0 ↔
      ¬ ringChar (IsLocalRing.ResidueField R) ∣ n := by
  rw [IsDiscreteValuationRing.addVal_eq_zero_iff,
    IsLocalRing.isUnit_natCast_iff_ringChar_not_dvd]

-- Ideal form of the ramification-index criterion, via both endpoints.
example {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)] :
    emultiplicity (IsLocalRing.maximalIdeal B)
        (Ideal.span
          {((IsLocalRing.maximalIdeal B).ramificationIdx A : B)}) =
        0 ↔
      ¬ ringChar (IsLocalRing.ResidueField B) ∣
        (IsLocalRing.maximalIdeal B).ramificationIdx A := by
  rw [IsDiscreteValuationRing.emultiplicity_maximalIdeal_span_eq_addVal,
    IsDiscreteValuationRing.addVal_eq_zero_iff,
    IsLocalRing.isUnit_natCast_iff_ringChar_not_dvd]

-- Concrete 5-adic case: `3` is a unit, so its ideal multiplicity vanishes.
-- The residue field of `ℤ_[5]` is `ZMod 5`, hence of characteristic 5.
example [Fact (Nat.Prime 5)] :
    emultiplicity (IsLocalRing.maximalIdeal ℤ_[5])
        (Ideal.span {((3 : ℕ) : ℤ_[5])}) = 0 := by
  have hchar : CharP (IsLocalRing.ResidueField ℤ_[5]) 5 :=
    charP_of_injective_ringHom
      (f := (PadicInt.residueField (p := 5)).symm.toRingHom)
      (PadicInt.residueField (p := 5)).symm.injective 5
  rw [IsDiscreteValuationRing.emultiplicity_maximalIdeal_span_eq_addVal,
    IsDiscreteValuationRing.addVal_eq_zero_iff,
    IsLocalRing.isUnit_natCast_iff_ringChar_not_dvd,
    ringChar.eq_iff.mpr hchar]
  decide
