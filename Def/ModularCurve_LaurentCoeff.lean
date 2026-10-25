import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField

namespace ModularCurve

section CoeffMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

def coeffMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := by
    ext k
    simp
  map_one' := by
    ext k
    simp [HahnSeries.coeff_one, apply_ite f]
  map_add' x y := by
    ext k
    simp
  map_mul' x y := by
    have h := HahnSeries.map_mul (f := (f : R →ₙ+* S)) (x := x) (y := y)
    have hx : ∀ z : LaurentSeries R, z.map (f : R →ₙ+* S) = z.map f := fun z =>
      HahnSeries.ext rfl
    rwa [hx, hx, hx] at h

end CoeffMap

section Constants

variable (L : Type*) [Field L]


variable [Algebra ℚ L]

def coeffEmb : LaurentSeries ℚ →+* LaurentSeries L :=
  coeffMap (algebraMap ℚ L)

end Constants

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

def laurentBaseChange : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))

end BaseChange

end ModularCurve

end
