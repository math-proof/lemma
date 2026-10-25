import Mathlib
import Lemma.ModularCurve.X0

noncomputable section

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

section LaurentMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

def laurentMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one (R := R) (S := S) f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (R := R) (S := S) f.toNonUnitalRingHom
  map_zero' := by
    ext k
    show f ((0 : LaurentSeries R).coeff k) = (0 : LaurentSeries S).coeff k
    rw [HahnSeries.coeff_zero, HahnSeries.coeff_zero, map_zero]
  map_add' x y := by
    ext k
    show f ((x + y).coeff k) = (x.map f + y.map f).coeff k
    rw [HahnSeries.coeff_add, HahnSeries.coeff_add, map_add]
    rfl

end LaurentMap

section IntegralJ

def jqInt : LaurentSeries ℤ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ jNum


def jqIntN (N : ℕ) [NeZero N] : LaurentSeries ℤ := qExpand ℤ N jqInt

end IntegralJ

section ReduceModBivar

def reduceModBivar (ℓ : ℕ) :
    Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial (ZMod ℓ)) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ)))

end ReduceModBivar

def KroneckerCongruence (ℓ : ℕ) [NeZero ℓ] (data : ModularPolynomialData ℓ) : Prop :=
  reduceModBivar ℓ data.Φ =
    (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) *
      (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ)

section IntegralEquation

def evalAtJInt : Polynomial ℤ →+* LaurentSeries ℤ :=
  Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) jqInt

end IntegralEquation

section ModEquation

variable (ℓ : ℕ)

def jqMod : LaurentSeries (ZMod ℓ) := laurentMap (Int.castRingHom (ZMod ℓ)) jqInt

def jqNMod (N : ℕ) [NeZero N] : LaurentSeries (ZMod ℓ) := qExpand (ZMod ℓ) N (jqMod ℓ)


def evalAtJMod : Polynomial (ZMod ℓ) →+* LaurentSeries (ZMod ℓ) :=
  Polynomial.eval₂RingHom (algebraMap (ZMod ℓ) (LaurentSeries (ZMod ℓ))) (jqMod ℓ)

end ModEquation

section ModFunctionField

variable (ℓ : ℕ) [Fact ℓ.Prime]

def modularFunctionFieldMod (N : ℕ) [NeZero N] :
    IntermediateField (ZMod ℓ) (LaurentSeries (ZMod ℓ)) :=
  IntermediateField.adjoin (ZMod ℓ) {jqMod ℓ, jqNMod ℓ N}

end ModFunctionField

end ModularCurve

end
