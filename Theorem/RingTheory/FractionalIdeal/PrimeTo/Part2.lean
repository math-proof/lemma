/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean -/

import Mathlib.RingTheory.FractionalIdeal.Extended
import Def.RingTheory.FractionalIdeal.PrimeTo
open scoped nonZeroDivisors

@[expose] noncomputable section

/-!
# Fractional ideals prime to an ideal

A fractional ideal is prime to an ideal when it becomes the unit ideal after localization at
every prime containing that ideal. The invertible fractional ideals with this property form a
subgroup.
-/


namespace FractionalIdeal

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The unit fractional ideal is prime to every ideal. -/
@[simp]
theorem isPrimeTo_one (J : Ideal A) :
    IsPrimeTo (1 : FractionalIdeal A⁰ (FractionRing A)) J := by
  intro p _ _
  exact FractionalIdeal.extended_one _ _

end FractionalIdeal
