/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean -/

import Mathlib.RingTheory.FractionalIdeal.Extended
import Theorem.RingTheory.FractionalIdeal.PrimeTo.Part2
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

/-- The subgroup of invertible fractional ideals prime to J. -/
def unitsPrimeTo (J : Ideal A) :
    Subgroup (FractionalIdeal A⁰ (FractionRing A))ˣ where
  carrier := {u | (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J}
  one_mem' := isPrimeTo_one J
  mul_mem' := fun ha hb => ha.mul hb
  inv_mem' := fun hu => hu.inv_unit

end FractionalIdeal
