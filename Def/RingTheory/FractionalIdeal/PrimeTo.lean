/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean -/

import Mathlib.RingTheory.FractionalIdeal.Extended
import Theorem.RingTheory.FractionalIdeal.PrimeTo
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

/-- A fractional ideal is prime to J if it becomes one at every prime containing J. -/
def IsPrimeTo (I : FractionalIdeal A⁰ (FractionRing A)) (J : Ideal A) : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], J ≤ p →
    FractionalIdeal.extended (FractionRing A)
      (nonZeroDivisors_le_comap_algebraMap_atPrime p) I = 1

end FractionalIdeal
