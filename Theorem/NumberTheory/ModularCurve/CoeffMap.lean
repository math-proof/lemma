/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Def.ModularCurve_LaurentCoeff

/-!
# Injectivity of coefficientwise ring maps of Laurent series

This file records `ModularCurve.coeffMap_injective`: if a ring homomorphism
is injective, then the induced map on Laurent series coefficients is injective.
-/

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

/-- If `f : R →+* S` is injective, then `coeffMap f` is injective. -/
theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (coeffMap f) :=
  fun x y hxy => by
    ext k
    exact hf (by simpa [coeffMap] using congrArg (fun z : LaurentSeries S => z.coeff k) hxy)

end ModularCurve

end
